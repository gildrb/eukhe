# ffi_dash: the entry of the compiled Bend core for the dashboard's
# pairing gate (bend/dash.bend; Rust: crates/eukhe-dashboard pairing.rs,
# http.rs, bridge.rs). The codec is the wire format of bend/wire.bend
# (crates/eukhe-bend/WIRE.md).
#
# The call answers one choice of what Rust met:
#
#   tag 0  token   a presented text (a Said)
#                  -> 0, the 32 bytes (List<Nat>) | 1 blank | 2 junk
#   tag 1  stored  a Disk  -> 0, the 32 bytes | 1 no token
#   tag 2  keep    a Rotation, a Disk, the file's mode (Nat)
#                  -> 0 mint | 1 reuse | 2 restrict | 3 unreadable
#                     | 4 tokenless
#
# The stepper is one socket (`Dm.Conn`): Rust opens it when the socket
# opens, sends each frame as it arrives with the token file read at that
# moment and whether its constant-time comparison found the socket's token
# equal to the file's, and does what the reply says.
#
#   open   nothing                          reply: empty
#   step   0, a First, a Disk, matches      (the socket's first frame)
#          | 1, a Disk, matches             (a later text frame)
#          reply: 0 paired | 1 run | 2, the text the tab shows (the
#          socket closes) | 3 closed (nothing runs)
#
#   Disk      0 none | 1 unreadable | 2 Holds{s: String} | 3 huge
#   Said      0 Spoken{s: String} | 1 overlong
#   First     0 no text | 1 not a pairing | 2 Pair{token: Said}
#   Rotation  0 keep | 1 rotate
#
# A malformed call, or one with input left over, answers
# `E dash: malformed request`; a malformed event, or one with input left
# over, answers `E dash: malformed event` and keeps the socket; an open
# with input opens the refused state, which answers every step
# `E dash: the open was refused`. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./dash.bend as Dm

# A request of the call
type Req is Data:
  QToken{said: Dm.Said}
  QStored{file: Dm.Disk}
  QKeep{rotation: Dm.Rotation, file: Dm.Disk, mode: Nat}

# Requests
# --------

def get_file.text(r: W.Dec<String>) -> W.Dec<Dm.Disk>:
  match r:
    case W.Got{t, s}:
      W.Got{Dm.Holds{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_file.tag(t: Nat, s: String) -> W.Dec<Dm.Disk>:
  match t:
    case 0n:
      W.Got{Dm.NoFile{}, s}
    case 1n:
      W.Got{Dm.Unread{}, s}
    case 2n:
      get_file.text(W.get_str(s))
    case 3n:
      W.Got{Dm.Huge{}, s}
    case 4n+u:
      W.Bad{}

def get_file(r: W.Dec<Nat>) -> W.Dec<Dm.Disk>:
  match r:
    case W.Got{t, s}:
      get_file.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_said.spoken(r: W.Dec<String>) -> W.Dec<Dm.Said>:
  match r:
    case W.Got{t, s}:
      W.Got{Dm.Spoken{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_said.tag(t: Nat, s: String) -> W.Dec<Dm.Said>:
  match t:
    case 0n:
      get_said.spoken(W.get_str(s))
    case 1n:
      W.Got{Dm.Overlong{}, s}
    case 2n+u:
      W.Bad{}

def get_said(r: W.Dec<Nat>) -> W.Dec<Dm.Said>:
  match r:
    case W.Got{t, s}:
      get_said.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_first.pair(r: W.Dec<Dm.Said>) -> W.Dec<Dm.First>:
  match r:
    case W.Got{t, s}:
      W.Got{Dm.Pair{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_first.tag(t: Nat, s: String) -> W.Dec<Dm.First>:
  match t:
    case 0n:
      W.Got{Dm.NoText{}, s}
    case 1n:
      W.Got{Dm.NotPairing{}, s}
    case 2n:
      get_first.pair(get_said(W.get_nat(s)))
    case 3n+u:
      W.Bad{}

def get_first(r: W.Dec<Nat>) -> W.Dec<Dm.First>:
  match r:
    case W.Got{t, s}:
      get_first.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_rotation.tag(t: Nat, s: String) -> W.Dec<Dm.Rotation>:
  match t:
    case 0n:
      W.Got{Dm.KeepToken{}, s}
    case 1n:
      W.Got{Dm.RotateToken{}, s}
    case 2n+u:
      W.Bad{}

def get_rotation(r: W.Dec<Nat>) -> W.Dec<Dm.Rotation>:
  match r:
    case W.Got{t, s}:
      get_rotation.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_token(r: W.Dec<Dm.Said>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QToken{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_stored(r: W.Dec<Dm.Disk>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      W.Got{QStored{f}, s}
    case W.Bad{}:
      W.Bad{}

def get_keep.mode(o: Dm.Rotation, f: Dm.Disk, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      W.Got{QKeep{o, f, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_keep.file(o: Dm.Rotation, r: W.Dec<Dm.Disk>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      get_keep.mode(o, f, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_keep(r: W.Dec<Dm.Rotation>) -> W.Dec<Req>:
  match r:
    case W.Got{o, s}:
      get_keep.file(o, get_file(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_token(get_said(W.get_nat(s)))
    case 1n:
      get_stored(get_file(W.get_nat(s)))
    case 2n:
      get_keep(get_rotation(W.get_nat(s)))
    case 3n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

def put_bytes(bs: List<&2, Nat>) -> String:
  W.put_nat(0n, W.put_list(~Nat, ~W.put_nat, bs, ""))

def put_shown(x: Dm.Shown) -> String:
  match x:
    case Dm.Hex{bs}:
      put_bytes(bs)
    case Dm.Blank{}:
      W.put_nat(1n, "")
    case Dm.Junk{}:
      W.put_nat(2n, "")

def put_stored(m: Maybe<&2, List<&2, Nat>>) -> String:
  match m:
    case Some{bs}:
      put_bytes(bs)
    case None{}:
      W.put_nat(1n, "")

def keep.tag(k: Dm.Keep) -> Nat:
  match k:
    case Dm.Mint{}:
      0n
    case Dm.Reuse{}:
      1n
    case Dm.Restrict{}:
      2n
    case Dm.Unreadable{}:
      3n
    case Dm.Tokenless{}:
      4n

# the reply of a request: the model's choice, encoded
def answer(q: Req) -> String:
  match q:
    case QToken{t}:
      put_shown(Dm.shown(t))
    case QStored{f}:
      put_stored(Dm.stored(f))
    case QKeep{o, f, m}:
      W.put_nat(keep.tag(Dm.keep(o, f, m)), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("dash: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("dash: malformed request")

# the call: decode the request, answer the model's choice
def ffi(input: String) -> String:
  ffi.got(get_req(input))

# The stepper
# -----------

def get_ev.matches(x: Dm.First, f: Dm.Disk, r: W.Dec<Bool>) -> W.Dec<Dm.CEv>:
  match r:
    case W.Got{b, s}:
      W.Got{Dm.CFirst{x, f, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.first(x: Dm.First, r: W.Dec<Dm.Disk>) -> W.Dec<Dm.CEv>:
  match r:
    case W.Got{f, s}:
      get_ev.matches(x, f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.pair(r: W.Dec<Dm.First>) -> W.Dec<Dm.CEv>:
  match r:
    case W.Got{x, s}:
      get_ev.first(x, get_file(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_ev.later(f: Dm.Disk, r: W.Dec<Bool>) -> W.Dec<Dm.CEv>:
  match r:
    case W.Got{b, s}:
      W.Got{Dm.CFrame{f, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.frame(r: W.Dec<Dm.Disk>) -> W.Dec<Dm.CEv>:
  match r:
    case W.Got{f, s}:
      get_ev.later(f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<Dm.CEv>:
  match t:
    case 0n:
      get_ev.pair(get_first(W.get_nat(s)))
    case 1n:
      get_ev.frame(get_file(W.get_nat(s)))
    case 2n+u:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<Dm.CEv>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the event at the start of s
def get_ev(s: String) -> W.Dec<Dm.CEv>:
  get_ev.go(W.get_nat(s))

def put_verdict(v: Dm.Verdict) -> String:
  match v:
    case Dm.VPaired{}:
      W.put_nat(0n, "")
    case Dm.VRun{}:
      W.put_nat(1n, "")
    case Dm.VRefuse{t}:
      W.put_nat(2n, W.put_str(t, ""))
    case Dm.VClosed{}:
      W.put_nat(3n, "")

# a socket, or a refused open
type St is Data:
  Live{c: Dm.Conn}
  Refused{}

def open.end(whole: Bool) -> St & String:
  match whole:
    case True{}:
      (Live{Dm.Waiting{}}, "")
    case False{}:
      (Refused{}, W.err("dash: the open takes no input"))

# open: a socket waiting for its pairing
def open(input: String) -> St & String:
  open.end(W.end(input))

def step.reply(r: Dm.Conn & Dm.Verdict) -> St & String:
  (c, v) = r
  (Live{c}, put_verdict(v))

def step.end(whole: Bool, +c: Dm.Conn, e: Dm.CEv) -> St & String:
  match whole:
    case True{}:
      step.reply(Dm.cstep(c, e))
    case False{}:
      (Live{c}, W.err("dash: malformed event"))

def step.ev(+c: Dm.Conn, r: W.Dec<Dm.CEv>) -> St & String:
  match r:
    case W.Got{e, rest}:
      step.end(W.end(rest), c, e)
    case W.Bad{}:
      (Live{c}, W.err("dash: malformed event"))

# step: one event; the reply is what Rust does
def step(st: St, input: String) -> St & String:
  match st:
    case Live{c}:
      step.ev(c, get_ev(input))
    case Refused{}:
      (Refused{}, W.err("dash: the open was refused"))
