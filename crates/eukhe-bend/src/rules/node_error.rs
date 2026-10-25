//! The Node-compatible failure of a native file system call
//! (`bend/node_error.bend`, entry `bend/ffi_node_error.bend`;
//! `laws/node_error.bend`): libuv's name and description of a code, the
//! file error code `toFileError` gives it, and the whole message of each
//! place a failed call names. [`describe`] encodes the code and the place,
//! calls [`Entry::NodeError`] and decodes the answer.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// A libuv error code (`Ne.Code`): the codes the host maps an OS error
/// number to; [`UvCode::Unknown`] for any other number and for an error
/// with no OS number.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UvCode {
    E2big,
    Eacces,
    Eagain,
    Ebadf,
    Ebusy,
    Ecanceled,
    Eexist,
    Efault,
    Efbig,
    Eintr,
    Einval,
    Eio,
    Eisdir,
    Eloop,
    Emfile,
    Emlink,
    Enametoolong,
    Enfile,
    Enodev,
    Enoent,
    Enoexec,
    Enomem,
    Enospc,
    Enosys,
    Enotdir,
    Enotempty,
    Enotsup,
    Enxio,
    Eoverflow,
    Eperm,
    Epipe,
    Erofs,
    Espipe,
    Esrch,
    Etimedout,
    Etxtbsy,
    Exdev,
    Unknown,
}

impl UvCode {
    /// The code's wire tag (`tag_spec` of `laws/node_error.bend`).
    fn tag(self) -> u32 {
        match self {
            UvCode::E2big => 0,
            UvCode::Eacces => 1,
            UvCode::Eagain => 2,
            UvCode::Ebadf => 3,
            UvCode::Ebusy => 4,
            UvCode::Ecanceled => 5,
            UvCode::Eexist => 6,
            UvCode::Efault => 7,
            UvCode::Efbig => 8,
            UvCode::Eintr => 9,
            UvCode::Einval => 10,
            UvCode::Eio => 11,
            UvCode::Eisdir => 12,
            UvCode::Eloop => 13,
            UvCode::Emfile => 14,
            UvCode::Emlink => 15,
            UvCode::Enametoolong => 16,
            UvCode::Enfile => 17,
            UvCode::Enodev => 18,
            UvCode::Enoent => 19,
            UvCode::Enoexec => 20,
            UvCode::Enomem => 21,
            UvCode::Enospc => 22,
            UvCode::Enosys => 23,
            UvCode::Enotdir => 24,
            UvCode::Enotempty => 25,
            UvCode::Enotsup => 26,
            UvCode::Enxio => 27,
            UvCode::Eoverflow => 28,
            UvCode::Eperm => 29,
            UvCode::Epipe => 30,
            UvCode::Erofs => 31,
            UvCode::Espipe => 32,
            UvCode::Esrch => 33,
            UvCode::Etimedout => 34,
            UvCode::Etxtbsy => 35,
            UvCode::Exdev => 36,
            UvCode::Unknown => 37,
        }
    }
}

/// What a failed call names (`Ne.Form`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Form<'a> {
    /// A call on an open descriptor: `CODE: description, syscall`.
    Fd { syscall: &'a str },
    /// A call on one path: `CODE: description, syscall 'path'`.
    Path { syscall: &'a str, path: &'a str },
    /// A call on two paths: `CODE: description, syscall 'path' -> 'dest'`.
    Dest {
        syscall: &'a str,
        path: &'a str,
        dest: &'a str,
    },
    /// A child process that did not start: `spawn program CODE`.
    Spawn { program: &'a str },
}

/// The file error code `toFileError` gives a Node error (`Ne.FileCode`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileCode {
    /// `ENOENT`.
    NotFound,
    /// `EACCES`, `EPERM`.
    PermissionDenied,
    /// `ENOTDIR`.
    NotDirectory,
    /// `EISDIR`.
    IsDirectory,
    /// `EINVAL`.
    Invalid,
    /// Every other code.
    Unknown,
}

/// The core's answer for a failed call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Described {
    pub file: FileCode,
    /// The message Node puts on the error.
    pub message: String,
}

/// The file error code and the message of a call that failed with `code`,
/// naming `form` (`Ne.file`, `Ne.message`).
///
/// # Errors
///
/// [`Error::Wire`] when a text is past [`crate::wire::STR_MAX`] chars; else
/// only from an inconsistent build (see [`crate::expect_core`]).
pub fn describe(code: UvCode, form: Form<'_>) -> Result<Described, Error> {
    let mut request = Writer::new();
    request.tag(code.tag());
    match form {
        Form::Fd { syscall } => {
            request.tag(0).str(syscall);
        }
        Form::Path { syscall, path } => {
            request.tag(1).str(syscall).str(path);
        }
        Form::Dest {
            syscall,
            path,
            dest,
        } => {
            request.tag(2).str(syscall).str(path).str(dest);
        }
        Form::Spawn { program } => {
            request.tag(3).str(program);
        }
    }
    let reply = call(Entry::NodeError, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let file = match reply.tag_of(6, "a file error code")? {
        0 => FileCode::NotFound,
        1 => FileCode::PermissionDenied,
        2 => FileCode::NotDirectory,
        3 => FileCode::IsDirectory,
        4 => FileCode::Invalid,
        _ => FileCode::Unknown,
    };
    let message = reply.str()?.to_owned();
    reply.end()?;
    Ok(Described { file, message })
}

#[cfg(test)]
mod tests {
    use super::{describe, Described, FileCode, Form, UvCode};

    #[test]
    fn the_codec_carries_each_form_through_the_core() {
        let renamed = Form::Dest {
            syscall: "rename",
            path: "a",
            dest: "b",
        };
        assert_eq!(
            [
                describe(UvCode::Eperm, renamed).unwrap(),
                describe(UvCode::Exdev, Form::Spawn { program: "sh" }).unwrap(),
            ],
            [
                Described {
                    file: FileCode::PermissionDenied,
                    message: "EPERM: operation not permitted, rename 'a' -> 'b'".to_owned(),
                },
                Described {
                    file: FileCode::Unknown,
                    message: "spawn sh EXDEV".to_owned(),
                },
            ]
        );
    }
}
