# ffi_node_error: the compiled Bend core's entry for the Node-compatible
# failure of a native file system call (bend/node_error.bend). Rust
# `eukhe_bend::rules::node_error::describe` calls it through
# `eukhe_bend::call` once per failed call (the error path only).
#
# Request (crates/eukhe-bend/WIRE.md): the code's tag (a Nat:
#   0 E2BIG, 1 EACCES, 2 EAGAIN, 3 EBADF, 4 EBUSY, 5 ECANCELED, 6 EEXIST,
#   7 EFAULT, 8 EFBIG, 9 EINTR, 10 EINVAL, 11 EIO, 12 EISDIR, 13 ELOOP,
#   14 EMFILE, 15 EMLINK, 16 ENAMETOOLONG, 17 ENFILE, 18 ENODEV, 19 ENOENT,
#   20 ENOEXEC, 21 ENOMEM, 22 ENOSPC, 23 ENOSYS, 24 ENOTDIR, 25 ENOTEMPTY,
#   26 ENOTSUP, 27 ENXIO, 28 EOVERFLOW, 29 EPERM, 30 EPIPE, 31 EROFS,
#   32 ESPIPE, 33 ESRCH, 34 ETIMEDOUT, 35 ETXTBSY, 36 EXDEV, 37 UNKNOWN),
# then the form, its tag then its fields:
#   0 fd     syscall (String)
#   1 path   syscall, path (Strings)
#   2 dest   syscall, path, dest (Strings)
#   3 spawn  program (String)
# Reply: the file error code (a Nat: 0 not found, 1 permission denied,
# 2 not a directory, 3 is a directory, 4 invalid, 5 unknown), then the
# message (String).
# A malformed request answers the error form "node_error: malformed
# request"; input left after the request answers "node_error: input left
# after the request": never a default. laws/node_error.bend (section
# entry) states this file's laws. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./node_error.bend as Ne

# A request of the entry
type Req is Data:
  Req{code: Ne.Code, form: Ne.Form}

# Requests
# --------

# the code of a tag
def code_of(t: Nat) -> Maybe<&2, Ne.Code>:
  match t:
    case 0n:
      Some{Ne.E2big{}}
    case 1n:
      Some{Ne.Eacces{}}
    case 2n:
      Some{Ne.Eagain{}}
    case 3n:
      Some{Ne.Ebadf{}}
    case 4n:
      Some{Ne.Ebusy{}}
    case 5n:
      Some{Ne.Ecanceled{}}
    case 6n:
      Some{Ne.Eexist{}}
    case 7n:
      Some{Ne.Efault{}}
    case 8n:
      Some{Ne.Efbig{}}
    case 9n:
      Some{Ne.Eintr{}}
    case 10n:
      Some{Ne.Einval{}}
    case 11n:
      Some{Ne.Eio{}}
    case 12n:
      Some{Ne.Eisdir{}}
    case 13n:
      Some{Ne.Eloop{}}
    case 14n:
      Some{Ne.Emfile{}}
    case 15n:
      Some{Ne.Emlink{}}
    case 16n:
      Some{Ne.Enametoolong{}}
    case 17n:
      Some{Ne.Enfile{}}
    case 18n:
      Some{Ne.Enodev{}}
    case 19n:
      Some{Ne.Enoent{}}
    case 20n:
      Some{Ne.Enoexec{}}
    case 21n:
      Some{Ne.Enomem{}}
    case 22n:
      Some{Ne.Enospc{}}
    case 23n:
      Some{Ne.Enosys{}}
    case 24n:
      Some{Ne.Enotdir{}}
    case 25n:
      Some{Ne.Enotempty{}}
    case 26n:
      Some{Ne.Enotsup{}}
    case 27n:
      Some{Ne.Enxio{}}
    case 28n:
      Some{Ne.Eoverflow{}}
    case 29n:
      Some{Ne.Eperm{}}
    case 30n:
      Some{Ne.Epipe{}}
    case 31n:
      Some{Ne.Erofs{}}
    case 32n:
      Some{Ne.Espipe{}}
    case 33n:
      Some{Ne.Esrch{}}
    case 34n:
      Some{Ne.Etimedout{}}
    case 35n:
      Some{Ne.Etxtbsy{}}
    case 36n:
      Some{Ne.Exdev{}}
    case 37n:
      Some{Ne.Unknown{}}
    case 38n+u:
      None{}

def get_code.of(m: Maybe<&2, Ne.Code>, s: String) -> W.Dec<Ne.Code>:
  match m:
    case Some{c}:
      W.Got{c, s}
    case None{}:
      W.Bad{}

# a code: its tag
def get_code(r: W.Dec<Nat>) -> W.Dec<Ne.Code>:
  match r:
    case W.Got{t, s}:
      get_code.of(code_of(t), s)
    case W.Bad{}:
      W.Bad{}

def get_fd(r: W.Dec<String>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{y, s}:
      W.Got{Ne.Fd{y}, s}
    case W.Bad{}:
      W.Bad{}

def get_path.path(y: String, r: W.Dec<String>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{p, s}:
      W.Got{Ne.Path{y, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_path(r: W.Dec<String>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{y, s}:
      get_path.path(y, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_dest.dest(y: String, p: String, r: W.Dec<String>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{d, s}:
      W.Got{Ne.Dest{y, p, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_dest.path(y: String, r: W.Dec<String>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{p, s}:
      get_dest.dest(y, p, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_dest(r: W.Dec<String>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{y, s}:
      get_dest.path(y, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_spawn(r: W.Dec<String>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{p, s}:
      W.Got{Ne.Spawn{p}, s}
    case W.Bad{}:
      W.Bad{}

# a form: its tag, then its fields
def get_form(r: W.Dec<Nat>) -> W.Dec<Ne.Form>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_fd(W.get_str(s))
        case 1n:
          get_path(W.get_str(s))
        case 2n:
          get_dest(W.get_str(s))
        case 3n:
          get_spawn(W.get_str(s))
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_req.form(c: Ne.Code, r: W.Dec<Ne.Form>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      W.Got{Req{c, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_req(r: W.Dec<Ne.Code>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_req.form(c, get_form(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# Replies
# -------

# the tag of a file error code
def put_file(f: Ne.FileCode, rest: String) -> String:
  match f:
    case Ne.NotFound{}:
      W.put_nat(0n, rest)
    case Ne.Denied{}:
      W.put_nat(1n, rest)
    case Ne.NotDir{}:
      W.put_nat(2n, rest)
    case Ne.IsDir{}:
      W.put_nat(3n, rest)
    case Ne.Invalid{}:
      W.put_nat(4n, rest)
    case Ne.Other{}:
      W.put_nat(5n, rest)

# The entry
# ---------

def ffi.done(q: Req, end: Bool) -> String:
  match q:
    case Req{+c, f}:
      match end:
        case True{}:
          put_file(Ne.file(c), W.put_str(Ne.message(c, f), ""))
        case False{}:
          W.err("node_error: input left after the request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("node_error: malformed request")

# the entry: decode the code and the form, answer the file error code and
# the message
def ffi(input: String) -> String:
  ffi.got(get_req(get_code(W.get_nat(input))))
