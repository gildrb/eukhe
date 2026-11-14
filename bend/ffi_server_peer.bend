# ffi_server_peer: the entry of the compiled Bend core for the server rule
# (bend/server_peer.bend; Rust: crates/eukhe-bend/src/rules/server_peer.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  four Nats: the listener's uid, the client's uid, the
#            listener's pid, the pid recorded for the endpoint (0: none)
#   reply    0 served | 1 another uid | 2 no record | 3 another pid
#
# Malformed input, or input left after the request, answers
# `E server_peer: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./server_peer.bend as Sp

# what Rust asks: the listener's uid, the client's uid, the listener's
# pid, the recorded pid
type Req is Data:
  Req{peer: Nat, own: Nat, pid: Nat, rec: Nat}

def get_req.rec(p: Nat, o: Nat, i: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      W.Got{Req{p, o, i, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.pid(p: Nat, o: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{i, s}:
      get_req.rec(p, o, i, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.own(p: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{o, s}:
      get_req.pid(p, o, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.peer(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_req.own(p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.peer(W.get_nat(s))

# the reply tag of a verdict
def tag(v: Sp.Served) -> Nat:
  match v:
    case Sp.Served{}:
      0n
    case Sp.OtherUid{}:
      1n
    case Sp.NoRecord{}:
      2n
    case Sp.OtherPid{}:
      3n

# the reply of a request: the model's verdict, encoded
def answer(q: Req) -> String:
  match q:
    case Req{p, o, i, c}:
      W.put_nat(tag(Sp.served(p, o, i, c)), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("server_peer: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("server_peer: malformed request")

# the entry: decode the request, answer the model's verdict
def ffi(input: String) -> String:
  ffi.got(get_req(input))
