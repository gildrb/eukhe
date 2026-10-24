# ffi_dash: the entry of the compiled Bend core for the dashboard's
# pairing choices (bend/dash.bend section 6; Rust: crates/eukhe-dashboard
# pairing.rs, http.rs, bridge.rs). Each request names one choice and
# carries what Rust met (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  token   a presented text (a Said)
#                  -> 0, the 32 bytes (List<Nat>) | 1 blank | 2 junk
#   tag 1  stored  a Disk  -> 0, the 32 bytes | 1 no token
#   tag 2  gate    a First, a Disk, same (Bool)
#                  -> 0 admit | 1, the text the tab shows (String)
#   tag 3  frame   a Disk, same (Bool)
#                  -> 0 run | 1, the text the tab shows
#   tag 4  keep    a Rotation, a Disk, the file's mode (Nat)
#                  -> 0 mint | 1 reuse | 2 restrict | 3 unreadable
#                     | 4 tokenless
#
#   Disk      0 none | 1 unreadable | 2 Holds{s: String} | 3 huge
#   Said      0 Spoken{s: String} | 1 overlong
#   First     0 no text | 1 not a pairing | 2 Pair{token: Said}
#   Rotation  0 keep | 1 rotate
#
# same: Rust found the presented and the stored token both decoded and
# equal (a constant-time comparison). Malformed input, or input left after
# the request, answers `E dash: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./dash.bend as Dm

# A request of the entry
type Req is Data:
  QToken{said: Dm.Said}
  QStored{file: Dm.Disk}
  QGate{first: Dm.First, file: Dm.Disk, same: Bool}
  QFrame{file: Dm.Disk, same: Bool}
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

def get_gate.same(x: Dm.First, f: Dm.Disk, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      W.Got{QGate{x, f, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_gate.file(x: Dm.First, r: W.Dec<Dm.Disk>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      get_gate.same(x, f, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_gate(r: W.Dec<Dm.First>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      get_gate.file(x, get_file(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_frame.same(f: Dm.Disk, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      W.Got{QFrame{f, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_frame(r: W.Dec<Dm.Disk>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      get_frame.same(f, W.get_bool(s))
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
      get_gate(get_first(W.get_nat(s)))
    case 3n:
      get_frame(get_file(W.get_nat(s)))
    case 4n:
      get_keep(get_rotation(W.get_nat(s)))
    case 5n+u:
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

def put_pass(p: Dm.Pass) -> String:
  match p:
    case Dm.Admit{}:
      W.put_nat(0n, "")
    case Dm.Refuse{t}:
      W.put_nat(1n, W.put_str(t, ""))

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
    case QGate{x, f, b}:
      put_pass(Dm.gate(x, f, b))
    case QFrame{f, b}:
      put_pass(Dm.frame(f, b))
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

# the entry: decode the request, answer the model's choice
def ffi(input: String) -> String:
  ffi.got(get_req(input))
