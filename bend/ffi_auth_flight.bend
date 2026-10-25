# ffi_auth_flight: the compiled Bend core's stepper for the OAuth refresh
# flights of one auth document (bend/auth_flight.bend section The desk the
# Rust runs). Rust `auth::flight` opens one per document, sends it each
# caller's events in the order they come and does what each reply says.
# Its state is the desk: the live callers and where each stands. The codec
# is the wire format of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    the empty input (an empty desk)               reply: empty
#   step    Ev
#   Ev      0 a caller arrives (provider: String)
#           1 a caller found (caller: Nat, what: Nat): 0 a fresh credential
#             at the load, 1 an expired one, 2 no refresh can start, 3 a
#             fresh credential at the check, 4 none, 5 a fetched
#             credential, 6 a failed fetch, 7 the store's outcome
#           2 a caller unwinds (caller: Nat)
#           3 how many wait on a provider's flight (provider: String)
#   reply to 0, 1, 2: a List of (caller: Nat, Act)
#   Act     0 load | 1 check | 2 fetch | 3 store this event's credential |
#           4 wait | 5 done with this event's payload | 6 failed (text:
#           String)
#   reply to 3: Maybe<Nat> (none: the provider has no flight in flight)
#
# The new caller of an arrival is the caller of its reply's one pair. An
# event that names no live caller, or a found the caller's place does not
# take, answers "auth_flight: out of turn" and keeps the desk. A malformed
# event (an unknown tag or what, a bad number, input left over) answers
# "auth_flight: malformed event" and keeps the desk; an open that is not
# empty answers "auth_flight: malformed open" and the refused stepper
# answers every step "auth_flight: the open was refused".
# laws/auth_flight.bend pins the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./auth_flight.bend as M

# the desk, or a refused open
type St is Data:
  Open{d: M.Desk}
  Shut{}

# The event
# ---------

def get_ev.what(k: Nat, t: Nat, s: String) -> W.Dec<M.DEv>:
  match t:
    case 0n:
      W.Got{M.Found{k, M.LoadFresh{}}, s}
    case 1n:
      W.Got{M.Found{k, M.LoadExpired{}}, s}
    case 2n:
      W.Got{M.Found{k, M.LoadFailed{}}, s}
    case 3n:
      W.Got{M.Found{k, M.CheckFresh{}}, s}
    case 4n:
      W.Got{M.Found{k, M.CheckExpired{}}, s}
    case 5n:
      W.Got{M.Found{k, M.FetchOk{}}, s}
    case 6n:
      W.Got{M.Found{k, M.FetchFailed{}}, s}
    case 7n:
      W.Got{M.Found{k, M.Stored{}}, s}
    case 8n+q:
      W.Bad{}

def get_ev.found(k: Nat, r: W.Dec<Nat>) -> W.Dec<M.DEv>:
  match r:
    case W.Got{t, s}:
      get_ev.what(k, t, s)
    case W.Bad{}:
      W.Bad{}

def get_ev.caller(r: W.Dec<Nat>) -> W.Dec<M.DEv>:
  match r:
    case W.Got{k, s}:
      get_ev.found(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.unwind(r: W.Dec<Nat>) -> W.Dec<M.DEv>:
  match r:
    case W.Got{k, s}:
      W.Got{M.Unwinds{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.comes(r: W.Dec<String>) -> W.Dec<M.DEv>:
  match r:
    case W.Got{p, s}:
      W.Got{M.Comes{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.joiners(r: W.Dec<String>) -> W.Dec<M.DEv>:
  match r:
    case W.Got{p, s}:
      W.Got{M.Joiners{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<M.DEv>:
  match t:
    case 0n:
      get_ev.comes(W.get_str(s))
    case 1n:
      get_ev.caller(W.get_nat(s))
    case 2n:
      get_ev.unwind(W.get_nat(s))
    case 3n:
      get_ev.joiners(W.get_str(s))
    case 4n+p:
      W.Bad{}

def get_ev(r: W.Dec<Nat>) -> W.Dec<M.DEv>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# The reply
# ---------

def put_act(a: M.Act, rest: String) -> String:
  match a:
    case M.DoLoad{}:
      W.put_nat(0n, rest)
    case M.DoCheck{}:
      W.put_nat(1n, rest)
    case M.DoFetch{}:
      W.put_nat(2n, rest)
    case M.DoStore{}:
      W.put_nat(3n, rest)
    case M.DoWait{}:
      W.put_nat(4n, rest)
    case M.DoDone{}:
      W.put_nat(5n, rest)
    case M.DoFail{e}:
      W.put_nat(6n, W.put_str(e, rest))

def put_tos(xs: List<&2, M.To>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      match x:
        case M.To{k, a}:
          W.put_nat(k, put_act(a, put_tos(t, rest)))

def put_out(o: M.DOut) -> String:
  match o:
    case M.Acts{+xs}:
      W.put_nat(List.length(&2, M.To, xs), put_tos(xs, ""))
    case M.Joined{j}:
      match j:
        case None{}:
          W.put_nat(0n, "")
        case Some{n}:
          W.put_nat(1n, W.put_nat(n, ""))
    case M.Off{}:
      W.err("auth_flight: out of turn")

# The stepper
# -----------

def open.fin(empty: Bool) -> St & String:
  match empty:
    case True{}:
      (Open{M.Desk.new()}, "")
    case False{}:
      (Shut{}, W.err("auth_flight: malformed open"))

# open: an empty desk
def open(input: String) -> St & String:
  open.fin(String.is_empty(input))

def step.put(r: M.DRes) -> St & String:
  match r:
    case M.DRes{d, o}:
      (Open{d}, put_out(o))

def step.fin(done: Bool, +d: M.Desk, e: M.DEv) -> St & String:
  match done:
    case True{}:
      step.put(M.desk.step(d, e))
    case False{}:
      (Open{d}, W.err("auth_flight: malformed event"))

def step.go(+d: M.Desk, r: W.Dec<M.DEv>) -> St & String:
  match r:
    case W.Got{e, s}:
      step.fin(W.end(s), d, e)
    case W.Bad{}:
      (Open{d}, W.err("auth_flight: malformed event"))

# step: one caller's event
def step(st: St, input: String) -> St & String:
  match st:
    case Open{+d}:
      step.go(d, get_ev(W.get_nat(input)))
    case Shut{}:
      (Shut{}, W.err("auth_flight: the open was refused"))
