# ffi_restart_turn: the entry of the compiled Bend core for what follows a
# run the supervisor ended (bend/restart_turn.bend; Rust: eukhe-bend
# rules/restart_turn.rs, asked by eukhe-daemon worker/create.rs and
# supervisor/supervision.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the facts, a tag (Nat): 0, then the automatic continues made
#            this turn (Nat): a reopen | 1 | 2 | 3: a give-up after a
#            Clear | Unsettled | Ended last relaunch
#   reply    what follows, a tag (Nat): 0, then n: Continue | 1, then n:
#            End | 2: Relaunch | 3: Retire
#
# Malformed input, or input left after the request, answers
# `E restart_turn: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./restart_turn.bend as Rt

def get_req.reopened(r: W.Dec<Nat>) -> W.Dec<Rt.Fact>:
  match r:
    case W.Got{n, s}:
      W.Got{Rt.Reopened{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Rt.Fact>:
  match t:
    case 0n:
      get_req.reopened(W.get_nat(s))
    case 1n:
      W.Got{Rt.GaveUp{Rt.Clear{}}, s}
    case 2n:
      W.Got{Rt.GaveUp{Rt.Unsettled{}}, s}
    case 3n:
      W.Got{Rt.GaveUp{Rt.Ended{}}, s}
    case 4n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Rt.Fact>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Rt.Fact>:
  get_req.start(W.get_nat(s))

# the reply's spelling of what follows
def put_next(x: Rt.Next) -> String:
  match x:
    case Rt.Continue{n}:
      W.put_nat(0n, W.put_nat(n, ""))
    case Rt.End{n}:
      W.put_nat(1n, W.put_nat(n, ""))
    case Rt.Relaunch{}:
      W.put_nat(2n, "")
    case Rt.Retire{}:
      W.put_nat(3n, "")

def ffi.done(f: Rt.Fact, end: Bool) -> String:
  match end:
    case True{}:
      put_next(Rt.next(f))
    case False{}:
      W.err("restart_turn: malformed request")

def ffi.got(r: W.Dec<Rt.Fact>) -> String:
  match r:
    case W.Got{f, +s}:
      ffi.done(f, W.end(s))
    case W.Bad{}:
      W.err("restart_turn: malformed request")

# the entry: decode the facts, answer what follows
def ffi(input: String) -> String:
  ffi.got(get_req(input))
