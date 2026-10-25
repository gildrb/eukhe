//! Node-compatible failures of native file system calls: the messages and
//! codes `node:fs` puts on its errors, and `toFileError` of `env/node.ts`,
//! which maps them to [`FileError`] codes. Rust maps the OS error number to
//! a libuv code ([`uv_code`]); the compiled core (`eukhe_bend::rules::
//! node_error`, `laws/node_error.bend`) gives the code's name and
//! description, its file error code and the whole message.

use std::io;
use std::sync::Arc;

use eukhe_bend::rules::node_error::{self, Described, FileCode, Form, UvCode};
use eukhe_bend::{expect_core, Entry};
use nix::errno::Errno;

use super::{FileError, FileErrorCode};

/// The libuv code of an OS error (`uv_translate_sys_error`): an error with
/// no OS number, or a number with no code here, is [`UvCode::Unknown`].
pub(crate) fn uv_code(error: &io::Error) -> UvCode {
    let Some(raw) = error.raw_os_error() else {
        return UvCode::Unknown;
    };
    match Errno::from_raw(raw) {
        Errno::E2BIG => UvCode::E2big,
        Errno::EACCES => UvCode::Eacces,
        Errno::EAGAIN => UvCode::Eagain,
        Errno::EBADF => UvCode::Ebadf,
        Errno::EBUSY => UvCode::Ebusy,
        Errno::ECANCELED => UvCode::Ecanceled,
        Errno::EEXIST => UvCode::Eexist,
        Errno::EFAULT => UvCode::Efault,
        Errno::EFBIG => UvCode::Efbig,
        Errno::EINTR => UvCode::Eintr,
        Errno::EINVAL => UvCode::Einval,
        Errno::EIO => UvCode::Eio,
        Errno::EISDIR => UvCode::Eisdir,
        Errno::ELOOP => UvCode::Eloop,
        Errno::EMFILE => UvCode::Emfile,
        Errno::EMLINK => UvCode::Emlink,
        Errno::ENAMETOOLONG => UvCode::Enametoolong,
        Errno::ENFILE => UvCode::Enfile,
        Errno::ENODEV => UvCode::Enodev,
        Errno::ENOENT => UvCode::Enoent,
        Errno::ENOEXEC => UvCode::Enoexec,
        Errno::ENOMEM => UvCode::Enomem,
        Errno::ENOSPC => UvCode::Enospc,
        Errno::ENOSYS => UvCode::Enosys,
        Errno::ENOTDIR => UvCode::Enotdir,
        Errno::ENOTEMPTY => UvCode::Enotempty,
        Errno::ENOTSUP => UvCode::Enotsup,
        Errno::ENXIO => UvCode::Enxio,
        Errno::EOVERFLOW => UvCode::Eoverflow,
        Errno::EPERM => UvCode::Eperm,
        Errno::EPIPE => UvCode::Epipe,
        Errno::EROFS => UvCode::Erofs,
        Errno::ESPIPE => UvCode::Espipe,
        Errno::ESRCH => UvCode::Esrch,
        Errno::ETIMEDOUT => UvCode::Etimedout,
        Errno::ETXTBSY => UvCode::Etxtbsy,
        Errno::EXDEV => UvCode::Exdev,
        _ => UvCode::Unknown,
    }
}

/// The file error code and the message Node gives a failure with `code`
/// of the call `form` names (the compiled core decides both).
///
/// # Panics
///
/// On a text past the core's wire bound (8 Mi chars) or an inconsistent
/// build ([`expect_core`]).
pub(crate) fn described(code: UvCode, form: Form<'_>) -> Described {
    expect_core(Entry::NodeError, node_error::describe(code, form))
}

/// `toFileError` of `error` for the call `form` names, with `error.path` =
/// `path`.
fn file_error(error: io::Error, form: Form<'_>, path: Option<String>) -> FileError {
    let Described { file, message } = described(uv_code(&error), form);
    let code = match file {
        FileCode::NotFound => FileErrorCode::NotFound,
        FileCode::PermissionDenied => FileErrorCode::PermissionDenied,
        FileCode::NotDirectory => FileErrorCode::NotDirectory,
        FileCode::IsDirectory => FileErrorCode::IsDirectory,
        FileCode::Invalid => FileErrorCode::Invalid,
        FileCode::Unknown => FileErrorCode::Unknown,
    };
    FileError::new(code, message, path).with_cause(Arc::new(error))
}

/// `toFileError` of the error Node throws when `syscall` on `path` fails:
/// message `CODE: description, syscall 'path'`, `error.path` = `path`.
pub(crate) fn fs_error(error: io::Error, syscall: &str, path: &str) -> FileError {
    file_error(error, Form::Path { syscall, path }, Some(path.to_owned()))
}

/// [`fs_error`] of a two-path call: message `CODE: description, syscall
/// 'path' -> 'dest'`, `error.path` = `path`.
pub(crate) fn fs_error_dest(error: io::Error, syscall: &str, path: &str, dest: &str) -> FileError {
    let form = Form::Dest {
        syscall,
        path,
        dest,
    };
    file_error(error, form, Some(path.to_owned()))
}

/// `toFileError(error, fallbackPath)` of a failed call on an open file
/// descriptor (`read`, `fstat`, `fsync`, ...), whose Node message names no
/// path: `CODE: description, syscall`.
pub(crate) fn fd_error(error: io::Error, syscall: &str, fallback_path: Option<&str>) -> FileError {
    file_error(
        error,
        Form::Fd { syscall },
        fallback_path.map(str::to_owned),
    )
}
