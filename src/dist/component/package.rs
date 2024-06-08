//! An interpreter for the rust-installer package format.  Responsible
//! for installing from a directory or tarball to an installation
//! prefix, represented by a `Components` instance.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io::{self, ErrorKind as IOErrorKind, Read};
use std::mem;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, bail, Context, Result};
use tar::EntryType;

use crate::diskio::{get_executor, CompletedIo, Executor, FileBuffer, Item, Kind, IO_CHUNK_SIZE};
use crate::dist::component::components::*;
use crate::dist::component::transaction::*;
use crate::dist::temp;
use crate::errors::*;
use crate::process;
use crate::utils::notifications::Notification;
use crate::utils::utils;

/// The current metadata revision used by rust-installer
pub(crate) const INSTALLER_VERSION: &str = "3";
pub(crate) const VERSION_FILE: &str = "rust-installer-version";

pub trait Package: fmt::Debug {
    fn contains(&self, component: &str, short_name: Option<&str>) -> bool;
    fn install<'a>(
        &self,
        target: &Components,
        component: &str,
        short_name: Option<&str>,
        tx: Transaction<'a>,
    ) -> Result<Transaction<'a>>;
    fn components(&self) -> Vec<String>;
}

#[derive(Debug)]
pub struct DirectoryPackage {
    path: PathBuf,
    components: HashSet<String>,
    copy: bool,
}

impl DirectoryPackage {
    pub fn new(path: PathBuf, copy: bool) -> Result<Self> {
        validate_installer_version(&path)?;

        let content = utils::read_file("package components", &path.join("components"))?;
        let components = content
            .lines()
            .map(std::borrow::ToOwned::to_owned)
            .collect();
        Ok(Self {
            path,
            components,
            copy,
        })
    }
}

fn validate_installer_version(path: &Path) -> Result<()> {
    let file = utils::read_file("installer version", &path.join(VERSION_FILE))?;
    let v = file.trim();
    if v == INSTALLER_VERSION {
        Ok(())
    } else {
        Err(anyhow!(format!("unsupported installer version: {v}")))
    }
}

impl Package for DirectoryPackage {
    fn contains(&self, component: &str, short_name: Option<&str>) -> bool {
        self.components.contains(component)
            || if let Some(n) = short_name {
                self.components.contains(n)
            } else {
                false
            }
    }
    fn install<'a>(
        &self,
        target: &Components,
        name: &str,
        short_name: Option<&str>,
        tx: Transaction<'a>,
    ) -> Result<Transaction<'a>> {
        let actual_name = if self.components.contains(name) {
            name
        } else if let Some(n) = short_name {
            n
        } else {
            name
        };

        let root = self.path.join(actual_name);

        let manifest = utils::read_file("package manifest", &root.join("manifest.in"))?;
        let mut builder = target.add(name, tx);

        for l in manifest.lines() {
            let part = ComponentPart::decode(l)
                .ok_or_else(|| RustupError::CorruptComponent(name.to_owned()))?;

            let path = part.1;
            let src_path = root.join(&path);

            match &*part.0 {
                "file" => {
                    if self.copy {
                        builder.copy_file(path.clone(), &src_path)?
                    } else {
                        builder.move_file(path.clone(), &src_path)?
                    }
                    nix_patchelf_if_needed(&target.prefix().path().join(path.clone()))
                }
                "dir" => {
                    if self.copy {
                        builder.copy_dir(path.clone(), &src_path)?
                    } else {
                        builder.move_dir(path.clone(), &src_path)?
                    }
                }
                _ => return Err(RustupError::CorruptComponent(name.to_owned()).into()),
            }
        }

        let tx = builder.finish()?;

        Ok(tx)
    }

    fn components(&self) -> Vec<String> {
        self.components.iter().cloned().collect()
    }
}

fn nix_wrap_lld(dest_lld_path: &Path) -> Result<()> {
    use std::fs;
    use std::io::Write;
    use std::os::unix::fs::PermissionsExt;

    let path = dest_lld_path.parent().unwrap();
    let mut unwrapped_name = path.file_name().unwrap().to_string_lossy().to_string();
    unwrapped_name.push_str("-unwrapped");
    let unwrapped_dir = path.with_file_name(unwrapped_name);
    fs::create_dir(&unwrapped_dir).context("failed to create unwrapped directory")?;
    let mut unwrapped_lld = unwrapped_dir;
    unwrapped_lld.push(dest_lld_path.file_name().unwrap());
    fs::rename(dest_lld_path, &unwrapped_lld).context("failed to move file")?;
    let mut ld_wrapper_path = std::env::current_exe()?
        .parent()
        .ok_or(anyhow!("failed to get parent directory"))?
        .with_file_name("nix-support");
    let mut file = std::fs::File::create(dest_lld_path)?;
    ld_wrapper_path.push("ld-wrapper.sh");

    let wrapped_script = format!(
        "#!/usr/bin/env bash
set -eu -o pipefail +o posix
shopt -s nullglob
export PROG=\"{}\"
\"{}\" $@",
        unwrapped_lld.to_string_lossy().to_string(),
        ld_wrapper_path.to_string_lossy().to_string(),
    );
    file.write_all(wrapped_script.as_bytes())?;
    let mut permissions = file.metadata()?.permissions();
    permissions.set_mode(0o755);
    file.set_permissions(permissions)?;
    Ok(())
}

fn nix_patchelf_if_needed(dest_path: &Path) {
    use std::fs::File;
    use std::os::unix::fs::FileExt;

    struct ELFReader<'a> {
        file: &'a mut File,
        is_32bit: bool,
        is_little_end: bool,
    }

    impl<'a> ELFReader<'a> {
        const MAGIC_NUMBER: &'static [u8] = &[0x7F, 0x45, 0x4c, 0x46];
        const ET_EXEC: u16 = 0x2;
        const ET_DYN: u16 = 0x3;
        const PT_INTERP: u32 = 0x3;

        fn new(file: &'a mut File) -> Option<Self> {
            let mut magic_number = [0; 4];
            file.read_exact(&mut magic_number).ok()?;
            if Self::MAGIC_NUMBER != magic_number {
                return None;
            }
            let mut ei_class = [0; 1];
            file.read_exact_at(&mut ei_class, 0x4).ok()?;
            let is_32bit = ei_class[0] == 1;
            let mut ei_data = [0; 1];
            file.read_exact_at(&mut ei_data, 0x5).ok()?;
            let is_little_end = ei_data[0] == 1;
            Some(Self {
                file,
                is_32bit,
                is_little_end,
            })
        }

        fn is_exec_or_dyn(&self) -> bool {
            let e_type = self.read_u16_at(0x10);
            e_type == Self::ET_EXEC || e_type == Self::ET_DYN
        }

        fn e_phoff(&self) -> u64 {
            if self.is_32bit {
                self.read_u32_at(0x1C) as u64
            } else {
                self.read_u64_at(0x20)
            }
        }

        fn e_phentsize(&self) -> u64 {
            let offset = if self.is_32bit { 0x2A } else { 0x36 };
            self.read_u16_at(offset) as u64
        }

        fn e_phnum(&self) -> u64 {
            let offset = if self.is_32bit { 0x2C } else { 0x38 };
            self.read_u16_at(offset) as u64
        }

        fn has_interp(&self) -> bool {
            let e_phoff = self.e_phoff();
            let e_phentsize = self.e_phentsize();
            let e_phnum = self.e_phnum();
            for i in 0..e_phnum {
                let p_type = self.read_u32_at(e_phoff + i * e_phentsize);
                if p_type == Self::PT_INTERP {
                    return true;
                }
            }
            false
        }

        fn read_u16_at(&self, offset: u64) -> u16 {
            let mut data = [0; 2];
            self.file.read_exact_at(&mut data, offset).unwrap();
            if self.is_little_end {
                u16::from_le_bytes(data)
            } else {
                u16::from_be_bytes(data)
            }
        }

        fn read_u32_at(&self, offset: u64) -> u32 {
            let mut data = [0; 4];
            self.file.read_exact_at(&mut data, offset).unwrap();
            if self.is_little_end {
                u32::from_le_bytes(data)
            } else {
                u32::from_be_bytes(data)
            }
        }

        fn read_u64_at(&self, offset: u64) -> u64 {
            let mut data = [0; 8];
            self.file.read_exact_at(&mut data, offset).unwrap();
            if self.is_little_end {
                u64::from_le_bytes(data)
            } else {
                u64::from_be_bytes(data)
            }
        }
    }

    let Some(mut dest_file) = File::open(dest_path).ok() else {
        return;
    };
    let Some(elf) = ELFReader::new(&mut dest_file) else {
        return;
    };
    if !elf.is_exec_or_dyn() {
        return;
    }
    let mut patch_command = std::process::Command::new("@patchelf@/bin/patchelf");
    if elf.has_interp() {
        patch_command
            .arg("--set-interpreter")
            .arg("@dynamicLinker@");
    }
    if Some(std::ffi::OsStr::new("rust-lld")) == dest_path.file_name() || !elf.has_interp() {
        patch_command.arg("--add-rpath").arg("@libPath@");
    }

    debug!("patching {dest_path:?} using patchelf");
    if let Err(err) = patch_command.arg(dest_path).output() {
        warn!("failed to execute patchelf: {err:?}");
    }

    if Some(std::ffi::OsStr::new("ld.lld")) == dest_path.file_name() {
        if let Err(err) = nix_wrap_lld(dest_path) {
            warn!("failed to wrap `ld.lld`: {err:?}");
        }
    }
}

#[derive(Debug)]
pub(crate) struct TarPackage<'a>(DirectoryPackage, temp::Dir<'a>);

impl<'a> TarPackage<'a> {
    pub(crate) fn new<R: Read>(
        stream: R,
        temp_cfg: &'a temp::Cfg,
        notify_handler: Option<&'a dyn Fn(Notification<'_>)>,
    ) -> Result<Self> {
        let temp_dir = temp_cfg.new_directory()?;
        let mut archive = tar::Archive::new(stream);
        // The rust-installer packages unpack to a directory called
        // $pkgname-$version-$target. Skip that directory when
        // unpacking.
        unpack_without_first_dir(&mut archive, &temp_dir, notify_handler)
            .context("failed to extract package (perhaps you ran out of disk space?)")?;

        Ok(TarPackage(
            DirectoryPackage::new(temp_dir.to_owned(), false)?,
            temp_dir,
        ))
    }
}

// Probably this should live in diskio but ¯\_(ツ)_/¯
fn unpack_ram(
    io_chunk_size: usize,
    effective_max_ram: Option<usize>,
    notify_handler: Option<&dyn Fn(Notification<'_>)>,
) -> usize {
    const RAM_ALLOWANCE_FOR_RUSTUP_AND_BUFFERS: usize = 200 * 1024 * 1024;
    let minimum_ram = io_chunk_size * 2;
    let default_max_unpack_ram = if let Some(effective_max_ram) = effective_max_ram {
        if effective_max_ram > minimum_ram + RAM_ALLOWANCE_FOR_RUSTUP_AND_BUFFERS {
            effective_max_ram - RAM_ALLOWANCE_FOR_RUSTUP_AND_BUFFERS
        } else {
            minimum_ram
        }
    } else {
        // Rustup does not know how much RAM the machine has: use the minimum
        minimum_ram
    };
    let unpack_ram = match process()
        .var("RUSTUP_UNPACK_RAM")
        .ok()
        .and_then(|budget_str| budget_str.parse::<usize>().ok())
    {
        Some(budget) => {
            if budget < minimum_ram {
                warn!(
                    "Ignoring RUSTUP_UNPACK_RAM ({}) less than minimum of {}.",
                    budget, minimum_ram
                );
                minimum_ram
            } else if budget > default_max_unpack_ram {
                warn!(
                    "Ignoring RUSTUP_UNPACK_RAM ({}) greater than detected available RAM of {}.",
                    budget, default_max_unpack_ram
                );
                default_max_unpack_ram
            } else {
                budget
            }
        }
        None => {
            if let Some(h) = notify_handler {
                h(Notification::SetDefaultBufferSize(default_max_unpack_ram))
            }
            default_max_unpack_ram
        }
    };

    if minimum_ram > unpack_ram {
        panic!("RUSTUP_UNPACK_RAM must be larger than {minimum_ram}");
    } else {
        unpack_ram
    }
}

/// Handle the async result of io operations
/// Replaces op.result with Ok(())
fn filter_result(op: &mut CompletedIo) -> io::Result<()> {
    if let CompletedIo::Item(op) = op {
        let result = mem::replace(&mut op.result, Ok(()));
        match result {
            Ok(_) => Ok(()),
            Err(e) => match e.kind() {
                IOErrorKind::AlreadyExists => {
                    // mkdir of e.g. ~/.rustup already existing is just fine;
                    // for others it would be better to know whether it is
                    // expected to exist or not -so put a flag in the state.
                    if let Kind::Directory = op.kind {
                        Ok(())
                    } else {
                        Err(e)
                    }
                }
                _ => Err(e),
            },
        }
    } else {
        Ok(())
    }
}

/// Dequeue the children of directories queued up waiting for the directory to
/// be created.
///
/// Currently the volume of queued items does not count as backpressure against
/// the main tar extraction process.
/// Returns the number of triggered children
fn trigger_children(
    io_executor: &dyn Executor,
    directories: &mut HashMap<PathBuf, DirStatus>,
    op: CompletedIo,
) -> Result<usize> {
    let mut result = 0;
    if let CompletedIo::Item(item) = op {
        if let Kind::Directory = item.kind {
            let mut pending = Vec::new();
            directories
                .entry(item.full_path)
                .and_modify(|status| match status {
                    DirStatus::Exists => unreachable!(),
                    DirStatus::Pending(pending_inner) => {
                        pending.append(pending_inner);
                        *status = DirStatus::Exists;
                    }
                })
                .or_insert_with(|| unreachable!());
            result += pending.len();
            for pending_item in pending.into_iter() {
                for mut item in io_executor.execute(pending_item).collect::<Vec<_>>() {
                    // TODO capture metrics
                    filter_result(&mut item)?;
                    result += trigger_children(io_executor, directories, item)?;
                }
            }
        }
    };
    Ok(result)
}

/// What is the status of this directory ?
enum DirStatus {
    Exists,
    Pending(Vec<Item>),
}

fn unpack_without_first_dir<R: Read>(
    archive: &mut tar::Archive<R>,
    path: &Path,
    notify_handler: Option<&dyn Fn(Notification<'_>)>,
) -> Result<()> {
    let entries = archive.entries()?;
    let effective_max_ram = match effective_limits::memory_limit() {
        Ok(ram) => Some(ram as usize),
        Err(e) => {
            if let Some(h) = notify_handler {
                h(Notification::Error(e.to_string()))
            }
            None
        }
    };
    let unpack_ram = unpack_ram(IO_CHUNK_SIZE, effective_max_ram, notify_handler);
    let mut io_executor: Box<dyn Executor> = get_executor(notify_handler, unpack_ram)?;

    let mut directories: HashMap<PathBuf, DirStatus> = HashMap::new();
    // Path is presumed to exist. Call it a precondition.
    directories.insert(path.to_owned(), DirStatus::Exists);

    'entries: for entry in entries {
        // drain completed results to keep memory pressure low and respond
        // rapidly to completed events even if we couldn't submit work (because
        // our unpacked item is pending dequeue)
        for mut item in io_executor.completed().collect::<Vec<_>>() {
            // TODO capture metrics
            filter_result(&mut item)?;
            trigger_children(&*io_executor, &mut directories, item)?;
        }

        let mut entry = entry?;
        let relpath = {
            let path = entry.path();
            let path = path?;
            path.into_owned()
        };
        // Reject path components that are not normal (..|/| etc)
        for part in relpath.components() {
            match part {
                // Some very early rust tarballs include a "." segment which we have to
                // support, despite not liking it.
                std::path::Component::Normal(_) | std::path::Component::CurDir => {}
                _ => bail!(format!("tar path '{}' is not supported", relpath.display())),
            }
        }
        let mut components = relpath.components();
        // Throw away the first path component: our root was supplied.
        components.next();
        let full_path = path.join(components.as_path());
        if full_path == path {
            // The tmp dir code makes the root dir for us.
            continue;
        }

        struct SenderEntry<'a, 'b, R: std::io::Read> {
            sender: Box<dyn FnMut(FileBuffer) -> bool + 'a>,
            entry: tar::Entry<'b, R>,
        }

        /// true if either no sender_entry was provided, or the incremental file
        /// has been fully dispatched.
        fn flush_ios<R: std::io::Read, P: AsRef<Path>>(
            io_executor: &mut dyn Executor,
            directories: &mut HashMap<PathBuf, DirStatus>,
            mut sender_entry: Option<&mut SenderEntry<'_, '_, R>>,
            full_path: P,
        ) -> Result<bool> {
            let mut result = sender_entry.is_none();
            for mut op in io_executor.completed().collect::<Vec<_>>() {
                // TODO capture metrics
                filter_result(&mut op)?;
                trigger_children(&*io_executor, directories, op)?;
            }
            // Maybe stream a file incrementally
            if let Some(sender) = sender_entry.as_mut() {
                if io_executor.buffer_available(IO_CHUNK_SIZE) {
                    let mut buffer = io_executor.get_buffer(IO_CHUNK_SIZE);
                    let len = sender
                        .entry
                        .by_ref()
                        .take(IO_CHUNK_SIZE as u64)
                        .read_to_end(&mut buffer)?;
                    buffer = buffer.finished();
                    if len == 0 {
                        result = true;
                    }
                    if !(sender.sender)(buffer) {
                        bail!(format!(
                            "IO receiver for '{}' disconnected",
                            full_path.as_ref().display()
                        ))
                    }
                }
            }
            Ok(result)
        }

        // Bail out if we get hard links, device nodes or any other unusual content
        // - it is most likely an attack, as rusts cross-platform nature precludes
        // such artifacts
        let kind = entry.header().entry_type();
        // https://github.com/rust-lang/rustup/issues/1140 and before that
        // https://github.com/rust-lang/rust/issues/25479
        // tl;dr: code got convoluted and we *may* have damaged tarballs out
        // there.
        // However the mandate we have is very simple: unpack as the current
        // user with modes matching the tar contents. No documented tars with
        // bad modes are in the bug tracker : the previous permission splatting
        // code was inherited from interactions with sudo that are best
        // addressed outside of rustup (run with an appropriate effective uid).
        // THAT SAID: If regressions turn up immediately post release this code -
        // https://play.rust-lang.org/?version=stable&mode=debug&edition=2018&gist=a8549057f0827bf3a068d8917256765a
        // is a translation of the prior helper function into an in-iterator
        // application.
        let tar_mode = entry.header().mode().ok().unwrap();
        // That said, the tarballs that are shipped way back have single-user
        // permissions:
        // -rwx------ rustbuild/rustbuild  ..... release/test-release.sh
        // so we should normalise the mode to match the previous behaviour users
        // may be expecting where the above file would end up with mode 0o755
        let u_mode = tar_mode & 0o700;
        let g_mode = (u_mode & 0o0500) >> 3;
        let o_mode = g_mode >> 3;
        let mode = u_mode | g_mode | o_mode;

        let file_size = entry.header().size()?;
        let size = std::cmp::min(IO_CHUNK_SIZE as u64, file_size);

        while !io_executor.buffer_available(size as usize) {
            flush_ios::<tar::Entry<'_, R>, _>(
                &mut *io_executor,
                &mut directories,
                None,
                &full_path,
            )?;
        }

        let mut incremental_file_sender: Option<Box<dyn FnMut(FileBuffer) -> bool + '_>> = None;
        let mut item = match kind {
            EntryType::Directory => {
                directories.insert(full_path.to_owned(), DirStatus::Pending(Vec::new()));
                Item::make_dir(full_path.clone(), mode)
            }
            EntryType::Regular => {
                if file_size > IO_CHUNK_SIZE as u64 {
                    let (item, sender) = Item::write_file_segmented(
                        full_path.clone(),
                        mode,
                        io_executor.incremental_file_state(),
                    )?;
                    incremental_file_sender = Some(sender);
                    item
                } else {
                    let mut content = io_executor.get_buffer(size as usize);
                    entry.read_to_end(&mut content)?;
                    content = content.finished();
                    Item::write_file(full_path.clone(), mode, content)
                }
            }
            _ => bail!(format!("tar entry kind '{kind:?}' is not supported")),
        };

        let item = loop {
            // Create the full path to the entry if it does not exist already
            if let Some(parent) = item.full_path.to_owned().parent() {
                match directories.get_mut(parent) {
                    None => {
                        // Tar has item before containing directory
                        // Complain about this so we can see if these exist.
                        writeln!(
                            process().stderr(),
                            "Unexpected: missing parent '{}' for '{}'",
                            parent.display(),
                            entry.path()?.display()
                        )?;
                        directories.insert(parent.to_owned(), DirStatus::Pending(vec![item]));
                        item = Item::make_dir(parent.to_owned(), 0o755);
                        // Check the parent's parent
                        continue;
                    }
                    Some(DirStatus::Exists) => {
                        break Some(item);
                    }
                    Some(DirStatus::Pending(pending)) => {
                        // Parent dir is being made
                        pending.push(item);
                        if incremental_file_sender.is_none() {
                            // take next item from tar
                            continue 'entries;
                        } else {
                            // don't submit a new item for processing, but do be ready to feed data to the incremental file.
                            break None;
                        }
                    }
                }
            } else {
                // We should never see a path with no parent.
                panic!();
            }
        };

        if let Some(item) = item {
            // Submit the new item
            for mut item in io_executor.execute(item).collect::<Vec<_>>() {
                // TODO capture metrics
                filter_result(&mut item)?;
                trigger_children(&*io_executor, &mut directories, item)?;
            }
        }

        let mut incremental_file_sender =
            incremental_file_sender.map(|incremental_file_sender| SenderEntry {
                sender: incremental_file_sender,
                entry,
            });

        // monitor io queue and feed in the content of the file (if needed)
        while !flush_ios(
            &mut *io_executor,
            &mut directories,
            incremental_file_sender.as_mut(),
            &full_path,
        )? {}
    }

    loop {
        let mut triggered = 0;
        for mut item in io_executor.join().collect::<Vec<_>>() {
            // handle final IOs
            // TODO capture metrics
            filter_result(&mut item)?;
            triggered += trigger_children(&*io_executor, &mut directories, item)?;
        }
        if triggered == 0 {
            // None of the IO submitted before the prior join triggered any new
            // submissions
            break;
        }
    }

    Ok(())
}

impl<'a> Package for TarPackage<'a> {
    fn contains(&self, component: &str, short_name: Option<&str>) -> bool {
        self.0.contains(component, short_name)
    }
    fn install<'b>(
        &self,
        target: &Components,
        component: &str,
        short_name: Option<&str>,
        tx: Transaction<'b>,
    ) -> Result<Transaction<'b>> {
        self.0.install(target, component, short_name, tx)
    }
    fn components(&self) -> Vec<String> {
        self.0.components()
    }
}

#[derive(Debug)]
pub(crate) struct TarGzPackage<'a>(TarPackage<'a>);

impl<'a> TarGzPackage<'a> {
    pub(crate) fn new<R: Read>(
        stream: R,
        temp_cfg: &'a temp::Cfg,
        notify_handler: Option<&'a dyn Fn(Notification<'_>)>,
    ) -> Result<Self> {
        let stream = flate2::read::GzDecoder::new(stream);
        Ok(TarGzPackage(TarPackage::new(
            stream,
            temp_cfg,
            notify_handler,
        )?))
    }
}

impl<'a> Package for TarGzPackage<'a> {
    fn contains(&self, component: &str, short_name: Option<&str>) -> bool {
        self.0.contains(component, short_name)
    }
    fn install<'b>(
        &self,
        target: &Components,
        component: &str,
        short_name: Option<&str>,
        tx: Transaction<'b>,
    ) -> Result<Transaction<'b>> {
        self.0.install(target, component, short_name, tx)
    }
    fn components(&self) -> Vec<String> {
        self.0.components()
    }
}

#[derive(Debug)]
pub(crate) struct TarXzPackage<'a>(TarPackage<'a>);

impl<'a> TarXzPackage<'a> {
    pub(crate) fn new<R: Read>(
        stream: R,
        temp_cfg: &'a temp::Cfg,
        notify_handler: Option<&'a dyn Fn(Notification<'_>)>,
    ) -> Result<Self> {
        let stream = xz2::read::XzDecoder::new(stream);
        Ok(TarXzPackage(TarPackage::new(
            stream,
            temp_cfg,
            notify_handler,
        )?))
    }
}

impl<'a> Package for TarXzPackage<'a> {
    fn contains(&self, component: &str, short_name: Option<&str>) -> bool {
        self.0.contains(component, short_name)
    }
    fn install<'b>(
        &self,
        target: &Components,
        component: &str,
        short_name: Option<&str>,
        tx: Transaction<'b>,
    ) -> Result<Transaction<'b>> {
        self.0.install(target, component, short_name, tx)
    }
    fn components(&self) -> Vec<String> {
        self.0.components()
    }
}

#[derive(Debug)]
pub(crate) struct TarZStdPackage<'a>(TarPackage<'a>);

impl<'a> TarZStdPackage<'a> {
    pub(crate) fn new<R: Read>(
        stream: R,
        temp_cfg: &'a temp::Cfg,
        notify_handler: Option<&'a dyn Fn(Notification<'_>)>,
    ) -> Result<Self> {
        let stream = zstd::stream::read::Decoder::new(stream)?;
        Ok(TarZStdPackage(TarPackage::new(
            stream,
            temp_cfg,
            notify_handler,
        )?))
    }
}

impl<'a> Package for TarZStdPackage<'a> {
    fn contains(&self, component: &str, short_name: Option<&str>) -> bool {
        self.0.contains(component, short_name)
    }
    fn install<'b>(
        &self,
        target: &Components,
        component: &str,
        short_name: Option<&str>,
        tx: Transaction<'b>,
    ) -> Result<Transaction<'b>> {
        self.0.install(target, component, short_name, tx)
    }
    fn components(&self) -> Vec<String> {
        self.0.components()
    }
}
