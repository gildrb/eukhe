# node_error: the Node-compatible failure of a native file system call
# (crates/eukhe-durable/src/env/node_error.rs; `node:fs` errors and
# `toFileError` of pi-durable `env/node.ts`). The Rust host maps the OS
# error number to a libuv code (`Code`, an OS ABI fact); the model gives
# the code's libuv name (`uv_err_name`) and description (`uv_strerror`),
# the file error code `toFileError` gives that name, and the whole message
# of each place a call names: `CODE: description, syscall` (a call on an
# open descriptor), `... syscall 'path'`, `... syscall 'path' -> 'dest'`,
# and the spawn failure `spawn program CODE`. `toFileError`'s ABORT_ERR arm
# is unreachable here: no libuv code is named ABORT_ERR. Pure: no IO, no
# @unsafe. laws/node_error.bend states its laws.

import Base

# Types
# -----

# a libuv error code (the codes eukhe's host maps an OS error number to;
# Unknown: any other number, or an error with no OS number)
type Code is Data:
  E2big{}
  Eacces{}
  Eagain{}
  Ebadf{}
  Ebusy{}
  Ecanceled{}
  Eexist{}
  Efault{}
  Efbig{}
  Eintr{}
  Einval{}
  Eio{}
  Eisdir{}
  Eloop{}
  Emfile{}
  Emlink{}
  Enametoolong{}
  Enfile{}
  Enodev{}
  Enoent{}
  Enoexec{}
  Enomem{}
  Enospc{}
  Enosys{}
  Enotdir{}
  Enotempty{}
  Enotsup{}
  Enxio{}
  Eoverflow{}
  Eperm{}
  Epipe{}
  Erofs{}
  Espipe{}
  Esrch{}
  Etimedout{}
  Etxtbsy{}
  Exdev{}
  Unknown{}

# the file error code `toFileError` gives a Node error
type FileCode is Data:
  # ENOENT
  NotFound{}
  # EACCES, EPERM
  Denied{}
  # ENOTDIR
  NotDir{}
  # EISDIR
  IsDir{}
  # EINVAL
  Invalid{}
  # any other code
  Other{}

# what the failed call names
type Form is Data:
  # a call on an open descriptor: no path
  Fd{syscall: String}
  # a call on one path
  Path{syscall: String, path: String}
  # a call on two paths (rename, copy, link)
  Dest{syscall: String, path: String, dest: String}
  # a child process that did not start
  Spawn{program: String}

# Texts
# -----

# libuv's name of a code (uv_err_name)
def name(c: Code) -> String:
  match c:
    case E2big{}:
      "E2BIG"
    case Eacces{}:
      "EACCES"
    case Eagain{}:
      "EAGAIN"
    case Ebadf{}:
      "EBADF"
    case Ebusy{}:
      "EBUSY"
    case Ecanceled{}:
      "ECANCELED"
    case Eexist{}:
      "EEXIST"
    case Efault{}:
      "EFAULT"
    case Efbig{}:
      "EFBIG"
    case Eintr{}:
      "EINTR"
    case Einval{}:
      "EINVAL"
    case Eio{}:
      "EIO"
    case Eisdir{}:
      "EISDIR"
    case Eloop{}:
      "ELOOP"
    case Emfile{}:
      "EMFILE"
    case Emlink{}:
      "EMLINK"
    case Enametoolong{}:
      "ENAMETOOLONG"
    case Enfile{}:
      "ENFILE"
    case Enodev{}:
      "ENODEV"
    case Enoent{}:
      "ENOENT"
    case Enoexec{}:
      "ENOEXEC"
    case Enomem{}:
      "ENOMEM"
    case Enospc{}:
      "ENOSPC"
    case Enosys{}:
      "ENOSYS"
    case Enotdir{}:
      "ENOTDIR"
    case Enotempty{}:
      "ENOTEMPTY"
    case Enotsup{}:
      "ENOTSUP"
    case Enxio{}:
      "ENXIO"
    case Eoverflow{}:
      "EOVERFLOW"
    case Eperm{}:
      "EPERM"
    case Epipe{}:
      "EPIPE"
    case Erofs{}:
      "EROFS"
    case Espipe{}:
      "ESPIPE"
    case Esrch{}:
      "ESRCH"
    case Etimedout{}:
      "ETIMEDOUT"
    case Etxtbsy{}:
      "ETXTBSY"
    case Exdev{}:
      "EXDEV"
    case Unknown{}:
      "UNKNOWN"

# libuv's description of a code (uv_strerror)
def description(c: Code) -> String:
  match c:
    case E2big{}:
      "argument list too long"
    case Eacces{}:
      "permission denied"
    case Eagain{}:
      "resource temporarily unavailable"
    case Ebadf{}:
      "bad file descriptor"
    case Ebusy{}:
      "resource busy or locked"
    case Ecanceled{}:
      "operation canceled"
    case Eexist{}:
      "file already exists"
    case Efault{}:
      "bad address in system call argument"
    case Efbig{}:
      "file too large"
    case Eintr{}:
      "interrupted system call"
    case Einval{}:
      "invalid argument"
    case Eio{}:
      "i/o error"
    case Eisdir{}:
      "illegal operation on a directory"
    case Eloop{}:
      "too many symbolic links encountered"
    case Emfile{}:
      "too many open files"
    case Emlink{}:
      "too many links"
    case Enametoolong{}:
      "name too long"
    case Enfile{}:
      "file table overflow"
    case Enodev{}:
      "no such device"
    case Enoent{}:
      "no such file or directory"
    case Enoexec{}:
      "exec format error"
    case Enomem{}:
      "not enough memory"
    case Enospc{}:
      "no space left on device"
    case Enosys{}:
      "function not implemented"
    case Enotdir{}:
      "not a directory"
    case Enotempty{}:
      "directory not empty"
    case Enotsup{}:
      "operation not supported on socket"
    case Enxio{}:
      "no such device or address"
    case Eoverflow{}:
      "value too large for defined data type"
    case Eperm{}:
      "operation not permitted"
    case Epipe{}:
      "broken pipe"
    case Erofs{}:
      "read-only file system"
    case Espipe{}:
      "invalid seek"
    case Esrch{}:
      "no such process"
    case Etimedout{}:
      "connection timed out"
    case Etxtbsy{}:
      "text file is busy"
    case Exdev{}:
      "cross-device link not permitted"
    case Unknown{}:
      "unknown error"

# the file error code of a code's name (toFileError)
def file(c: Code) -> FileCode:
  match c:
    case E2big{}:
      Other{}
    case Eacces{}:
      Denied{}
    case Eagain{}:
      Other{}
    case Ebadf{}:
      Other{}
    case Ebusy{}:
      Other{}
    case Ecanceled{}:
      Other{}
    case Eexist{}:
      Other{}
    case Efault{}:
      Other{}
    case Efbig{}:
      Other{}
    case Eintr{}:
      Other{}
    case Einval{}:
      Invalid{}
    case Eio{}:
      Other{}
    case Eisdir{}:
      IsDir{}
    case Eloop{}:
      Other{}
    case Emfile{}:
      Other{}
    case Emlink{}:
      Other{}
    case Enametoolong{}:
      Other{}
    case Enfile{}:
      Other{}
    case Enodev{}:
      Other{}
    case Enoent{}:
      NotFound{}
    case Enoexec{}:
      Other{}
    case Enomem{}:
      Other{}
    case Enospc{}:
      Other{}
    case Enosys{}:
      Other{}
    case Enotdir{}:
      NotDir{}
    case Enotempty{}:
      Other{}
    case Enotsup{}:
      Other{}
    case Enxio{}:
      Other{}
    case Eoverflow{}:
      Other{}
    case Eperm{}:
      Denied{}
    case Epipe{}:
      Other{}
    case Erofs{}:
      Other{}
    case Espipe{}:
      Other{}
    case Esrch{}:
      Other{}
    case Etimedout{}:
      Other{}
    case Etxtbsy{}:
      Other{}
    case Exdev{}:
      Other{}
    case Unknown{}:
      Other{}

# the message Node puts on the error of a call that failed with c
def message(+c: Code, f: Form) -> String:
  match f:
    case Fd{s}:
      String.append(String.concat([name(c), ": ", description(c), ", "]), s)
    case Path{s, p}:
      String.concat([name(c), ": ", description(c), ", ", s, " '", p, "'"])
    case Dest{s, p, d}:
      String.concat([name(c), ": ", description(c), ", ", s, " '", p, "' -> '", d, "'"])
    case Spawn{prog}:
      String.append(String.concat(["spawn ", prog, " "]), name(c))
