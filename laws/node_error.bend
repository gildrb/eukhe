# eukhe: the laws of area node_error

import Base
import ../bend/node_error.bend as Ne
import ../bend/ffi_node_error.bend as FNe
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1): the Node-compatible failure of a native file system call
# (bend/node_error.bend, the port of eukhe-durable env/node_error.rs
# `uv_error_name`, `file_error_code`, `fs_error`, `fs_error_dest`,
# `fd_error` and the spawn message of env/native/exec.rs). Each law is an
# open claim about Ne.name, Ne.description, Ne.file or Ne.message;
# PROOF.bend proves them (as NodeError.<law>) with the lemmas of
# proof/node_error/.
#
# R1: each libuv code has libuv's name (uv_err_name) and description
#     (uv_strerror) of the table below; an OS error the host maps to no
#     code is UNKNOWN, "unknown error".
# R2: the file error code is toFileError's of the name: ENOENT not found,
#     EACCES and EPERM permission denied, ENOTDIR not a directory, EISDIR
#     is a directory, EINVAL invalid, every other name unknown
#     (toFileError's ABORT_ERR arm never applies: no code is named
#     ABORT_ERR).
# R3: the message is "<NAME>: <description>, <syscall>" for a call on an
#     open descriptor, then " '<path>'" for a call on a path, then
#     " -> '<dest>'" for a call on two paths; a child that did not start
#     is "spawn <program> <NAME>". Every syscall, path, dest and program is
#     free text, kept exactly.

# Terms
# -----

# R1: libuv's (name, description) of each code
def row_spec(c: Ne.Code) -> String & String:
  match c:
    case Ne.E2big{}:
      ("E2BIG", "argument list too long")
    case Ne.Eacces{}:
      ("EACCES", "permission denied")
    case Ne.Eagain{}:
      ("EAGAIN", "resource temporarily unavailable")
    case Ne.Ebadf{}:
      ("EBADF", "bad file descriptor")
    case Ne.Ebusy{}:
      ("EBUSY", "resource busy or locked")
    case Ne.Ecanceled{}:
      ("ECANCELED", "operation canceled")
    case Ne.Eexist{}:
      ("EEXIST", "file already exists")
    case Ne.Efault{}:
      ("EFAULT", "bad address in system call argument")
    case Ne.Efbig{}:
      ("EFBIG", "file too large")
    case Ne.Eintr{}:
      ("EINTR", "interrupted system call")
    case Ne.Einval{}:
      ("EINVAL", "invalid argument")
    case Ne.Eio{}:
      ("EIO", "i/o error")
    case Ne.Eisdir{}:
      ("EISDIR", "illegal operation on a directory")
    case Ne.Eloop{}:
      ("ELOOP", "too many symbolic links encountered")
    case Ne.Emfile{}:
      ("EMFILE", "too many open files")
    case Ne.Emlink{}:
      ("EMLINK", "too many links")
    case Ne.Enametoolong{}:
      ("ENAMETOOLONG", "name too long")
    case Ne.Enfile{}:
      ("ENFILE", "file table overflow")
    case Ne.Enodev{}:
      ("ENODEV", "no such device")
    case Ne.Enoent{}:
      ("ENOENT", "no such file or directory")
    case Ne.Enoexec{}:
      ("ENOEXEC", "exec format error")
    case Ne.Enomem{}:
      ("ENOMEM", "not enough memory")
    case Ne.Enospc{}:
      ("ENOSPC", "no space left on device")
    case Ne.Enosys{}:
      ("ENOSYS", "function not implemented")
    case Ne.Enotdir{}:
      ("ENOTDIR", "not a directory")
    case Ne.Enotempty{}:
      ("ENOTEMPTY", "directory not empty")
    case Ne.Enotsup{}:
      ("ENOTSUP", "operation not supported on socket")
    case Ne.Enxio{}:
      ("ENXIO", "no such device or address")
    case Ne.Eoverflow{}:
      ("EOVERFLOW", "value too large for defined data type")
    case Ne.Eperm{}:
      ("EPERM", "operation not permitted")
    case Ne.Epipe{}:
      ("EPIPE", "broken pipe")
    case Ne.Erofs{}:
      ("EROFS", "read-only file system")
    case Ne.Espipe{}:
      ("ESPIPE", "invalid seek")
    case Ne.Esrch{}:
      ("ESRCH", "no such process")
    case Ne.Etimedout{}:
      ("ETIMEDOUT", "connection timed out")
    case Ne.Etxtbsy{}:
      ("ETXTBSY", "text file is busy")
    case Ne.Exdev{}:
      ("EXDEV", "cross-device link not permitted")
    case Ne.Unknown{}:
      ("UNKNOWN", "unknown error")

# the name of a row
def row_name(r: String & String) -> String:
  match r:
    case (n, d):
      n

def file_spec.pick(same: Bool, yes: Ne.FileCode, no: Ne.FileCode) -> Ne.FileCode:
  match same:
    case True{}:
      yes
    case False{}:
      no

# yes when n is t, else no
def file_spec.is(+n: String, t: String, yes: Ne.FileCode, no: Ne.FileCode) -> Ne.FileCode:
  file_spec.pick(String.eq(n, t), yes, no)

# R2: toFileError's code of a Node error named n
def file_spec(+n: String) -> Ne.FileCode:
  file_spec.is(n, "ENOENT", Ne.NotFound{}, file_spec.is(n, "EACCES", Ne.Denied{}, file_spec.is(n, "EPERM", Ne.Denied{}, file_spec.is(n, "ENOTDIR", Ne.NotDir{}, file_spec.is(n, "EISDIR", Ne.IsDir{}, file_spec.is(n, "EINVAL", Ne.Invalid{}, Ne.Other{}))))))

# R3: the message of a row and a form
def message_spec.of(r: String & String, f: Ne.Form) -> String:
  match r:
    case (n, d):
      match f:
        case Ne.Fd{s}:
          String.append(String.concat([n, ": ", d, ", "]), s)
        case Ne.Path{s, p}:
          String.concat([n, ": ", d, ", ", s, " '", p, "'"])
        case Ne.Dest{s, p, t}:
          String.concat([n, ": ", d, ", ", s, " '", p, "' -> '", t, "'"])
        case Ne.Spawn{prog}:
          String.append(String.concat(["spawn ", prog, " "]), n)

# R3: the message of a call that failed with c, naming f
def message_spec(c: Ne.Code, f: Ne.Form) -> String:
  message_spec.of(row_spec(c), f)

# Laws
# ----

# LAW node_error_table_exact: every code has the name and the description of the libuv table R1
# EXCLUDES: a misspelled, swapped or shared name or description, a code
#   answered with another code's row, a changed word of UNKNOWN
law node_error_table_exact:
  for +c: Ne.Code
  {(Ne.name(c), Ne.description(c)) == row_spec(c) : String & String}

# LAW node_error_file_exact: every code's file error code is toFileError's of its name: not found, permission denied (EACCES and EPERM), not a directory, is a directory, invalid, else unknown
# EXCLUDES: EPERM or EACCES left unknown, another code mapped to a known
#   file error code, ENOTDIR and EISDIR swapped
law node_error_file_exact:
  for +c: Ne.Code
  {Ne.file(c) == file_spec(row_name(row_spec(c))) : Ne.FileCode}

# LAW node_error_message_exact: the message of every code and every place is exactly R3: the name, the description, the syscall, then the quoted path and dest; a spawn names the program and the code
# EXCLUDES: a missing or added space, comma, quote or arrow, the path and
#   dest swapped, a path dropped or shown for a call on a descriptor, the
#   description where the spawn names the code, any changed char of a
#   syscall, path, dest or program
law node_error_message_exact:
  for +c: Ne.Code
  for f: Ne.Form
  {Ne.message(c, f) == message_spec(c, f) : String}

# LAW node_error_example: anchor: the messages and file error codes Node gives a missing file, a refused rename, a bad descriptor, an unknown error and a spawn
# EXCLUDES: a spec that is wrong on the shipped messages
law node_error_example:
  {Ne.message(Ne.Enoent{}, Ne.Path{"open", "/a/b"}) == "ENOENT: no such file or directory, open '/a/b'" : String} &
  {Ne.message(Ne.Eperm{}, Ne.Dest{"rename", "a", "b"}) == "EPERM: operation not permitted, rename 'a' -> 'b'" : String} &
  {Ne.message(Ne.Ebadf{}, Ne.Fd{"read"}) == "EBADF: bad file descriptor, read" : String} &
  {Ne.message(Ne.Unknown{}, Ne.Fd{"write"}) == "UNKNOWN: unknown error, write" : String} &
  {Ne.message(Ne.Enoent{}, Ne.Spawn{"sh"}) == "spawn sh ENOENT" : String} &
  {Ne.file(Ne.Eperm{}) == Ne.Denied{} : Ne.FileCode} &
  {Ne.file(Ne.Eloop{}) == Ne.Other{} : Ne.FileCode}

# LAWS (R4): the entry of the compiled Bend core (bend/ffi_node_error.bend,
# called by crates/eukhe-durable env through
# `eukhe_bend::rules::node_error`). Each law is an open claim about
# FNe.ffi, stated with spec spellers built only from the wire primitives
# of bend/wire.bend (their round trips: laws/wire.bend).
#
# R4: a request is the code's tag (a Nat, tag_spec below), then the form:
#     tag 0 and the syscall (a call on a descriptor), tag 1, the syscall
#     and the path, tag 2, the syscall, the path and the dest, or tag 3
#     and the program (Strings). The reply is the file error code's tag
#     (0 not found, 1 permission denied, 2 not a directory, 3 is a
#     directory, 4 invalid, 5 unknown), then the message (a String). A
#     malformed request answers the error form "node_error: malformed
#     request", input left after the request "node_error: input left after
#     the request", never a default.

# Spec spellers
# -------------

# R4: the wire tag of each code
def tag_spec(c: Ne.Code) -> Nat:
  match c:
    case Ne.E2big{}:
      0n
    case Ne.Eacces{}:
      1n
    case Ne.Eagain{}:
      2n
    case Ne.Ebadf{}:
      3n
    case Ne.Ebusy{}:
      4n
    case Ne.Ecanceled{}:
      5n
    case Ne.Eexist{}:
      6n
    case Ne.Efault{}:
      7n
    case Ne.Efbig{}:
      8n
    case Ne.Eintr{}:
      9n
    case Ne.Einval{}:
      10n
    case Ne.Eio{}:
      11n
    case Ne.Eisdir{}:
      12n
    case Ne.Eloop{}:
      13n
    case Ne.Emfile{}:
      14n
    case Ne.Emlink{}:
      15n
    case Ne.Enametoolong{}:
      16n
    case Ne.Enfile{}:
      17n
    case Ne.Enodev{}:
      18n
    case Ne.Enoent{}:
      19n
    case Ne.Enoexec{}:
      20n
    case Ne.Enomem{}:
      21n
    case Ne.Enospc{}:
      22n
    case Ne.Enosys{}:
      23n
    case Ne.Enotdir{}:
      24n
    case Ne.Enotempty{}:
      25n
    case Ne.Enotsup{}:
      26n
    case Ne.Enxio{}:
      27n
    case Ne.Eoverflow{}:
      28n
    case Ne.Eperm{}:
      29n
    case Ne.Epipe{}:
      30n
    case Ne.Erofs{}:
      31n
    case Ne.Espipe{}:
      32n
    case Ne.Esrch{}:
      33n
    case Ne.Etimedout{}:
      34n
    case Ne.Etxtbsy{}:
      35n
    case Ne.Exdev{}:
      36n
    case Ne.Unknown{}:
      37n

def spell_code(c: Ne.Code, rest: String) -> String:
  Wr.put_nat(tag_spec(c), rest)

def spell_form(f: Ne.Form, rest: String) -> String:
  match f:
    case Ne.Fd{s}:
      Wr.put_nat(0n, Wr.put_str(s, rest))
    case Ne.Path{s, p}:
      Wr.put_nat(1n, Wr.put_str(s, Wr.put_str(p, rest)))
    case Ne.Dest{s, p, t}:
      Wr.put_nat(2n, Wr.put_str(s, Wr.put_str(p, Wr.put_str(t, rest))))
    case Ne.Spawn{prog}:
      Wr.put_nat(3n, Wr.put_str(prog, rest))

# a request: the code, the form, then rest
def spell_req(q: FNe.Req, rest: String) -> String:
  match q:
    case FNe.Req{c, f}:
      spell_code(c, spell_form(f, rest))

def spell_file(k: Ne.FileCode, rest: String) -> String:
  match k:
    case Ne.NotFound{}:
      Wr.put_nat(0n, rest)
    case Ne.Denied{}:
      Wr.put_nat(1n, rest)
    case Ne.NotDir{}:
      Wr.put_nat(2n, rest)
    case Ne.IsDir{}:
      Wr.put_nat(3n, rest)
    case Ne.Invalid{}:
      Wr.put_nat(4n, rest)
    case Ne.Other{}:
      Wr.put_nat(5n, rest)

# the answer R1-R4 give a request
def answer_spec(q: FNe.Req) -> String:
  match q:
    case FNe.Req{+c, f}:
      spell_file(file_spec(row_name(row_spec(c))), Wr.put_str(message_spec(c, f), ""))

# every text of the form fits the wire
def form_fits(f: Ne.Form) -> Bool:
  match f:
    case Ne.Fd{+s}:
      LawsBase.wire_fits(String.length(s))
    case Ne.Path{+s, +p}:
      Bool.and(LawsBase.wire_fits(String.length(s)), LawsBase.wire_fits(String.length(p)))
    case Ne.Dest{+s, +p, +t}:
      Bool.and(LawsBase.wire_fits(String.length(s)), Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(t))))
    case Ne.Spawn{+prog}:
      LawsBase.wire_fits(String.length(prog))

# every text of the request fits the wire
def req_fits(q: FNe.Req) -> Bool:
  match q:
    case FNe.Req{c, f}:
      form_fits(f)

# a request with more input after it: the request, then a char and the
# rest
type LeftOver is Data:
  LeftOver{req: FNe.Req, head: Char, tail: String}

# the request of a left-over input
def left_req(w: LeftOver) -> FNe.Req:
  match w:
    case LeftOver{q, h, t}:
      q

def spell_left_over(w: LeftOver) -> String:
  match w:
    case LeftOver{q, h, t}:
      spell_req(q, SCon{h, t})

# Laws
# ----

# LAW node_error_ffi_answers: a spelled request whose texts fit the wire answers the spelled file error code and message of R1-R3
# EXCLUDES: a code read as another code (a tag off by one, two tags
#   swapped), a form read as another, the syscall, path and dest swapped,
#   the file error code and the message in another order or spelling
law node_error_ffi_answers:
  for +q: FNe.Req
  for fit: {req_fits(q) == True{} : Bool}
  {FNe.ffi(spell_req(q, "")) == answer_spec(q) : String}

# LAW node_error_ffi_exact: every input the entry answers with a value (not the error form) is a spelled request whose texts fit the wire
# EXCLUDES: a default answer for a malformed request (a code tag past 37,
#   a form tag past 3, a missing or short text, a Nat of 15 or more
#   digits) or one with input left over
law node_error_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FNe.ffi(s)) == False{} : Bool}
  exs q: FNe.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW node_error_ffi_left_over: a request that fits the wire, followed by more input, answers the left-over error form
# EXCLUDES: the input after the request ignored or read as part of it
law node_error_ffi_left_over:
  for +q: FNe.Req
  for +h: Char
  for +t: String
  for fit: {req_fits(q) == True{} : Bool}
  {FNe.ffi(spell_req(q, SCon{h, t})) == Wr.err("node_error: input left after the request") : String}

# LAW node_error_ffi_left_over_exact: the entry answers the left-over error form only for a spelled request that fits the wire, followed by more input
# EXCLUDES: the left-over text for a malformed request
law node_error_ffi_left_over_exact:
  for +s: String
  for e: {FNe.ffi(s) == Wr.err("node_error: input left after the request") : String}
  exs w: LeftOver
  {s == spell_left_over(w) : String} & {req_fits(left_req(w)) == True{} : Bool}

# LAW node_error_ffi_errors: every error the entry answers is the malformed or the left-over error form; with node_error_ffi_exact and node_error_ffi_left_over_exact, every input that spells no request answers exactly "node_error: malformed request"
# EXCLUDES: another error text
law node_error_ffi_errors:
  for +s: String
  for e: {LawsBase.wire_opens_err(FNe.ffi(s)) == True{} : Bool}
  {Bool.or(LawsBase.text_same(FNe.ffi(s), Wr.err("node_error: malformed request")), LawsBase.text_same(FNe.ffi(s), Wr.err("node_error: input left after the request"))) == True{} : Bool}

# LAW node_error_ffi_example: anchor: the exact bytes Rust sends for a missing file, a refused rename, a bad descriptor and a spawn, and four refusals
# EXCLUDES: another spelling of a request or of an answer, a default for
#   an unknown code or form tag
law node_error_ffi_example:
  {FNe.ffi("19,1,4,open4,/a/b") == "0,46,ENOENT: no such file or directory, open '/a/b'" : String} &
  {FNe.ffi("29,2,6,rename1,a1,b") == "1,49,EPERM: operation not permitted, rename 'a' -> 'b'" : String} &
  {FNe.ffi("3,0,4,read") == "5,32,EBADF: bad file descriptor, read" : String} &
  {FNe.ffi("37,3,2,sh") == "5,16,spawn sh UNKNOWN" : String} &
  {FNe.ffi("38,0,4,read") == Wr.err("node_error: malformed request") : String} &
  {FNe.ffi("19,4,4,read") == Wr.err("node_error: malformed request") : String} &
  {FNe.ffi("19,1,4,open9,/a") == Wr.err("node_error: malformed request") : String} &
  {FNe.ffi("19,0,4,readx") == Wr.err("node_error: input left after the request") : String}
