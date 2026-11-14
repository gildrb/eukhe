# ffi_once: the entry of the compiled Bend core for one effect across
# restarts (bend/once.bend; Rust: eukhe-bend rules/once.rs). A stepper
# and a call. The stepper's state is the effect's life, kept in the Bend
# heap: Rust opens it, sends each record of the effect's journal in the
# order the journal holds them, then asks what the restart does. The call
# `ffi` answers an effect's idempotency key. The codec is the wire format
# of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   open    (empty)                                reply: Life
#   step    Ev                                     reply: Life | Verdict
#   Ev      0 a record: Rec                        reply: the Life after it
#           | 1 the restart asks: Mode, Policy, Seen
#                                                  reply: the Verdict (the
#                                                  life is kept)
#   Rec     0 intended, 1 started, 2 finished, 3 unknown, 4 unstarted
#   Mode    0 resume, 1 stop
#   Policy  0 never | 1 safe | 2 keyed: cap (Nat), Dedup
#   Dedup   0 undeclared, 1 lasting
#   Seen    0 dark, 1 landed, 2 clean
#   Life    0 absent | 1 pending | 2 running: again (Nat) | 3 ran
#           | 4 lost | 5 void
#   Verdict 0 skip, 1 launch, 2 adopt, 3 interrupt, 4 abandon, 5 settled
#
#   ffi     scope: String, id: String              reply: the key, as text
#                                                  (the scope, then the id,
#                                                  each a String)
#
# A malformed event, or one with input left over, answers
# `E once: malformed event` and keeps the life; an open with any input
# opens the refused state, which answers every step with
# `E once: the open was refused`; a call input that is not exactly two
# Strings answers `E once: malformed key`. laws/once.bend pins the entry.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./once.bend as O

# What Rust sends a stepper
type Ev is Data:
  Note{r: O.Rec}
  Ask{m: O.Mode, p: O.Policy, s: O.Seen}

# Decoders
# --------

def get_rec.tag(n: Nat, s: String) -> W.Dec<O.Rec>:
  match n:
    case 0n:
      W.Got{O.Intended{}, s}
    case 1n:
      W.Got{O.Started{}, s}
    case 2n:
      W.Got{O.Finished{}, s}
    case 3n:
      W.Got{O.Unknown{}, s}
    case 4n:
      W.Got{O.Unstarted{}, s}
    case 5n+p:
      W.Bad{}

def get_rec.go(r: W.Dec<Nat>) -> W.Dec<O.Rec>:
  match r:
    case W.Got{n, s}:
      get_rec.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_rec(s: String) -> W.Dec<O.Rec>:
  get_rec.go(W.get_nat(s))

def get_mode.tag(n: Nat, s: String) -> W.Dec<O.Mode>:
  match n:
    case 0n:
      W.Got{O.Resume{}, s}
    case 1n:
      W.Got{O.Stop{}, s}
    case 2n+p:
      W.Bad{}

def get_mode.go(r: W.Dec<Nat>) -> W.Dec<O.Mode>:
  match r:
    case W.Got{n, s}:
      get_mode.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_mode(s: String) -> W.Dec<O.Mode>:
  get_mode.go(W.get_nat(s))

def get_policy.dedup.tag(cap: Nat, n: Nat, s: String) -> W.Dec<O.Policy>:
  match n:
    case 0n:
      W.Got{O.Keyed{O.Undeclared{}, cap}, s}
    case 1n:
      W.Got{O.Keyed{O.Lasting{}, cap}, s}
    case 2n+p:
      W.Bad{}

def get_policy.dedup(cap: Nat, r: W.Dec<Nat>) -> W.Dec<O.Policy>:
  match r:
    case W.Got{n, s}:
      get_policy.dedup.tag(cap, n, s)
    case W.Bad{}:
      W.Bad{}

def get_policy.cap(r: W.Dec<Nat>) -> W.Dec<O.Policy>:
  match r:
    case W.Got{cap, s}:
      get_policy.dedup(cap, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_policy.tag(n: Nat, s: String) -> W.Dec<O.Policy>:
  match n:
    case 0n:
      W.Got{O.Never{}, s}
    case 1n:
      W.Got{O.Safe{}, s}
    case 2n:
      get_policy.cap(W.get_nat(s))
    case 3n+p:
      W.Bad{}

def get_policy.go(r: W.Dec<Nat>) -> W.Dec<O.Policy>:
  match r:
    case W.Got{n, s}:
      get_policy.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_policy(s: String) -> W.Dec<O.Policy>:
  get_policy.go(W.get_nat(s))

def get_seen.tag(n: Nat, s: String) -> W.Dec<O.Seen>:
  match n:
    case 0n:
      W.Got{O.Dark{}, s}
    case 1n:
      W.Got{O.Landed{}, s}
    case 2n:
      W.Got{O.Clean{}, s}
    case 3n+p:
      W.Bad{}

def get_seen.go(r: W.Dec<Nat>) -> W.Dec<O.Seen>:
  match r:
    case W.Got{n, s}:
      get_seen.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_seen(s: String) -> W.Dec<O.Seen>:
  get_seen.go(W.get_nat(s))

def get_ev.note(r: W.Dec<O.Rec>) -> W.Dec<Ev>:
  match r:
    case W.Got{x, s}:
      W.Got{Note{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.seen(m: O.Mode, p: O.Policy, r: W.Dec<O.Seen>) -> W.Dec<Ev>:
  match r:
    case W.Got{x, s}:
      W.Got{Ask{m, p, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.policy(m: O.Mode, r: W.Dec<O.Policy>) -> W.Dec<Ev>:
  match r:
    case W.Got{p, s}:
      get_ev.seen(m, p, get_seen(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.mode(r: W.Dec<O.Mode>) -> W.Dec<Ev>:
  match r:
    case W.Got{m, s}:
      get_ev.policy(m, get_policy(s))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(n: Nat, s: String) -> W.Dec<Ev>:
  match n:
    case 0n:
      get_ev.note(get_rec(s))
    case 1n:
      get_ev.mode(get_mode(s))
    case 2n+p:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<Ev>:
  match r:
    case W.Got{n, s}:
      get_ev.tag(n, s)
    case W.Bad{}:
      W.Bad{}

# the event at the start of s
def get_ev(s: String) -> W.Dec<Ev>:
  get_ev.go(W.get_nat(s))

# Encoders
# --------

def put_life(l: O.Life) -> String:
  match l:
    case O.Absent{}:
      W.put_nat(0n, "")
    case O.Pending{}:
      W.put_nat(1n, "")
    case O.Running{again}:
      W.put_nat(2n, W.put_nat(again, ""))
    case O.Ran{}:
      W.put_nat(3n, "")
    case O.Unsure{}:
      W.put_nat(4n, "")
    case O.Void{}:
      W.put_nat(5n, "")

def put_verdict(v: O.Verdict) -> String:
  match v:
    case O.Skip{}:
      W.put_nat(0n, "")
    case O.Launch{}:
      W.put_nat(1n, "")
    case O.Adopt{}:
      W.put_nat(2n, "")
    case O.Interrupt{}:
      W.put_nat(3n, "")
    case O.Abandon{}:
      W.put_nat(4n, "")
    case O.Settled{}:
      W.put_nat(5n, "")

# The stepper
# -----------

# the effect's life, or a refused open
type St is Data:
  Eff{l: O.Life}
  Refused{}

def open.end(done: Bool) -> St & String:
  match done:
    case True{}:
      (Eff{O.Absent{}}, put_life(O.Absent{}))
    case False{}:
      (Refused{}, W.err("once: malformed open"))

# open: an effect with no record yet
def open(input: String) -> St & String:
  open.end(W.end(input))

def fail() -> String:
  W.err("once: malformed event")

# a record moves the life and answers it
def step.note(l: O.Life) -> St & String:
  +n = l
  (Eff{n}, put_life(n))

# one event on the life l
def step.ev(e: Ev, +l: O.Life) -> St & String:
  match e:
    case Note{r}:
      step.note(O.life.step(l, r))
    case Ask{m, p, s}:
      (Eff{l}, put_verdict(O.recover(l, s, m, p)))

def step.end(done: Bool, e: Ev, +l: O.Life) -> St & String:
  match done:
    case True{}:
      step.ev(e, l)
    case False{}:
      (Eff{l}, fail())

def step.got(d: W.Dec<Ev>, +l: O.Life) -> St & String:
  match d:
    case W.Got{e, rest}:
      step.end(W.end(rest), e, l)
    case W.Bad{}:
      (Eff{l}, fail())

# step: one event of the effect; a refused open answers the error form
def step(s: St, input: String) -> St & String:
  match s:
    case Eff{+l}:
      step.got(get_ev(input), l)
    case Refused{}:
      (Refused{}, W.err("once: the open was refused"))

# The key
# -------

def ffi.end(done: Bool, scope: String, id: String) -> String:
  match done:
    case True{}:
      O.key(scope, id)
    case False{}:
      W.err("once: malformed key")

def ffi.id(scope: String, d: W.Dec<String>) -> String:
  match d:
    case W.Got{id, rest}:
      ffi.end(W.end(rest), scope, id)
    case W.Bad{}:
      W.err("once: malformed key")

def ffi.scope(d: W.Dec<String>) -> String:
  match d:
    case W.Got{scope, rest}:
      ffi.id(scope, W.get_str(rest))
    case W.Bad{}:
      W.err("once: malformed key")

# the call: the idempotency key of the effect `id` of `scope`
def ffi(input: String) -> String:
  ffi.scope(W.get_str(input))
