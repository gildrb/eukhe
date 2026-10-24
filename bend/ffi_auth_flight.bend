# ffi_auth_flight: the compiled Bend core's entry for the decisions of
# the OAuth refresh flights (bend/auth_flight.bend section The decisions
# the Rust takes). Rust `auth::flight` calls it: the call after each read,
# fetch or write of a leg, the stepper (one per auth document) for the
# book of the document's flights.
#
# Call (crates/eukhe-bend/WIRE.md): a tag, what the step found (then the
# flight for 3 to 7): 0 a fresh credential at the load, 1 an expired one,
# 2 no refresh can start; 3 a fresh credential at the check, 4 none; 5 a
# fetched credential, 6 a failed fetch; 7 the store wrote.
# Reply: a tag, the leg that follows: 0 board, 1 fetch, 2 store, 3 land
# (then the flight for 1 to 3), 4 done.
#
# Stepper: open on the empty input (an empty book; the reply is empty).
# An event: a tag, then 0 board (the provider: String), 1 land (the
# provider, the flight: Nat), 2 wait (the flight), 3 joiners (the
# provider). Reply: a tag: 0 lead (then the flight), 1 join (then the
# flight), 2 kept, 3 dropped, 4 not yet, 5 take, 6 take last, 7 joiners
# (then a Maybe<Nat>).
#
# Malformed input answers the error form: "auth_flight: malformed
# request" (a call), "auth_flight: malformed open" (an open that is not
# empty: the stepper stays refused, "auth_flight: the open was refused"),
# "auth_flight: malformed event" (the book stays as it was).

import Base
import ./wire.bend as W
import ./auth_flight.bend as M

# The call
# --------

def get_io.mk(t: Nat, f: Nat) -> M.Io:
  match t:
    case 0n:
      M.CheckFresh{f}
    case 1n:
      M.CheckExpired{f}
    case 2n:
      M.FetchOk{f}
    case 3n:
      M.FetchFailed{f}
    case 4n+p:
      M.Stored{f}

def get_io.of(t: Nat, r: W.Dec<Nat>) -> W.Dec<M.Io>:
  match r:
    case W.Got{f, s}:
      W.Got{get_io.mk(t, f), s}
    case W.Bad{}:
      W.Bad{}

def get_io.tag(t: Nat, s: String) -> W.Dec<M.Io>:
  match t:
    case 0n:
      W.Got{M.LoadFresh{}, s}
    case 1n:
      W.Got{M.LoadExpired{}, s}
    case 2n:
      W.Got{M.LoadFailed{}, s}
    case 3n+p:
      match p:
        case 0n:
          get_io.of(0n, W.get_nat(s))
        case 1n:
          get_io.of(1n, W.get_nat(s))
        case 2n:
          get_io.of(2n, W.get_nat(s))
        case 3n:
          get_io.of(3n, W.get_nat(s))
        case 4n:
          get_io.of(4n, W.get_nat(s))
        case 5n+q:
          W.Bad{}

def get_io(r: W.Dec<Nat>) -> W.Dec<M.Io>:
  match r:
    case W.Got{t, s}:
      get_io.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def put_next(x: M.Next) -> String:
  match x:
    case M.NBoard{}:
      W.put_nat(0n, "")
    case M.NFetch{f}:
      W.put_nat(1n, W.put_nat(f, ""))
    case M.NStore{f}:
      W.put_nat(2n, W.put_nat(f, ""))
    case M.NLand{f}:
      W.put_nat(3n, W.put_nat(f, ""))
    case M.NDone{}:
      W.put_nat(4n, "")

def ffi.fin(done: Bool, io: M.Io) -> String:
  match done:
    case True{}:
      put_next(M.next(io))
    case False{}:
      W.err("auth_flight: malformed request")

def ffi.go(r: W.Dec<M.Io>) -> String:
  match r:
    case W.Got{io, s}:
      ffi.fin(W.end(s), io)
    case W.Bad{}:
      W.err("auth_flight: malformed request")

def ffi(input: String) -> String:
  ffi.go(get_io(W.get_nat(input)))

# The stepper
# -----------

type St is Data:
  Open{b: M.Book}
  Shut{}

def get_ev.land(p: String, r: W.Dec<Nat>) -> W.Dec<M.BEv>:
  match r:
    case W.Got{f, s}:
      W.Got{M.EvLand{p, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.kind(t: Nat, p: String, s: String) -> W.Dec<M.BEv>:
  match t:
    case 0n:
      W.Got{M.EvBoard{p}, s}
    case 1n:
      get_ev.land(p, W.get_nat(s))
    case 2n+q:
      W.Got{M.EvJoiners{p}, s}

def get_ev.named(t: Nat, r: W.Dec<String>) -> W.Dec<M.BEv>:
  match r:
    case W.Got{p, s}:
      get_ev.kind(t, p, s)
    case W.Bad{}:
      W.Bad{}

def get_ev.wait(r: W.Dec<Nat>) -> W.Dec<M.BEv>:
  match r:
    case W.Got{f, s}:
      W.Got{M.EvWait{f}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<M.BEv>:
  match t:
    case 0n:
      get_ev.named(0n, W.get_str(s))
    case 1n:
      get_ev.named(1n, W.get_str(s))
    case 2n:
      get_ev.wait(W.get_nat(s))
    case 3n:
      get_ev.named(2n, W.get_str(s))
    case 4n+p:
      W.Bad{}

def get_ev(r: W.Dec<Nat>) -> W.Dec<M.BEv>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def put_out(o: M.BOut) -> String:
  match o:
    case M.OLead{f}:
      W.put_nat(0n, W.put_nat(f, ""))
    case M.OJoin{f}:
      W.put_nat(1n, W.put_nat(f, ""))
    case M.OKept{}:
      W.put_nat(2n, "")
    case M.ODropped{}:
      W.put_nat(3n, "")
    case M.ONotYet{}:
      W.put_nat(4n, "")
    case M.OTake{}:
      W.put_nat(5n, "")
    case M.OTakeLast{}:
      W.put_nat(6n, "")
    case M.OJoiners{m}:
      match m:
        case None{}:
          W.put_nat(7n, W.put_nat(0n, ""))
        case Some{j}:
          W.put_nat(7n, W.put_nat(1n, W.put_nat(j, "")))

def open.fin(empty: Bool) -> St & String:
  match empty:
    case True{}:
      (Open{M.Book.new()}, "")
    case False{}:
      (Shut{}, W.err("auth_flight: malformed open"))

# open: an empty book
def open(input: String) -> St & String:
  open.fin(String.is_empty(input))

def step.put(r: M.BRes) -> St & String:
  match r:
    case M.BRes{b, o}:
      (Open{b}, put_out(o))

def step.fin(done: Bool, +b: M.Book, e: M.BEv) -> St & String:
  match done:
    case True{}:
      step.put(M.book.step(b, e))
    case False{}:
      (Open{b}, W.err("auth_flight: malformed event"))

def step.go(+b: M.Book, r: W.Dec<M.BEv>) -> St & String:
  match r:
    case W.Got{e, s}:
      step.fin(W.end(s), b, e)
    case W.Bad{}:
      (Open{b}, W.err("auth_flight: malformed event"))

# step: one event of the book
def step(st: St, input: String) -> St & String:
  match st:
    case Open{+b}:
      step.go(b, get_ev(W.get_nat(input)))
    case Shut{}:
      (Shut{}, W.err("auth_flight: the open was refused"))
