# wait: the model of one wait of the harness (docs/harness.md, H6). A
# wait races three things: the event it waits for, a deadline, and the
# cancel signal. It sees them one at a time, in any order the adversary
# picks; the first one ends it, and nothing after that changes the end.
#
# Time is counted in ticks. A deadline of d ticks passes on the d-th
# tick; a deadline of 0 has passed before anything happens. The Rust race
# (`eukhe_chord::context::race`) is checked against this model by the
# bridge (bend/bridge_wait.bend, crates/eukhe-core/src/memory/service/turn/bridge.rs).

import Base

# What a wait sees
type Sig is Data:
  Arrive{}  # the event it waits for
  Tick{}    # one tick of time
  Cancel{}  # the cancel signal fires

# How a wait ends
type End is Data:
  Arrived{}
  Expired{}
  Cancelled{}

# A wait: open, or over. `left` is None without a deadline; Some{m}: the
# deadline passes on the (m + 1)-th tick from now.
type W is Data:
  Open{left: Maybe<&2, Nat>}
  Over{}

# The state after one tick
def tick(left: Maybe<&2, Nat>) -> W:
  match left:
    case None{}:
      Open{None{}}
    case Some{m}:
      match m:
        case 0n:
          Over{}
        case 1n+q:
          Open{Some{q}}

# What one tick ends: Expired when the deadline passes
def tick.out(left: Maybe<&2, Nat>) -> List<&2, End>:
  match left:
    case None{}:
      Nil{}
    case Some{m}:
      match m:
        case 0n:
          [Expired{}]
        case 1n+q:
          Nil{}

# The state after one signal
def next(w: W, s: Sig) -> W:
  match w:
    case Over{}:
      Over{}
    case Open{left}:
      match s:
        case Arrive{}:
          Over{}
        case Tick{}:
          tick(left)
        case Cancel{}:
          Over{}

# What one signal ends
def out(w: W, s: Sig) -> List<&2, End>:
  match w:
    case Over{}:
      Nil{}
    case Open{left}:
      match s:
        case Arrive{}:
          [Arrived{}]
        case Tick{}:
          tick.out(left)
        case Cancel{}:
          [Cancelled{}]

# Every end a wait in state w reports while it sees xs, in order
def go(xs: List<&2, Sig>, +w: W) -> List<&2, End>:
  match xs:
    case Nil{}:
      Nil{}
    case +s <> rest:
      List.append(&2, End, out(w, s), go(rest, next(w, s)))

# A wait with deadline dl (None: none; Some{d}: d ticks) that sees xs:
# every end it reports
def run(dl: Maybe<&2, Nat>, xs: List<&2, Sig>) -> List<&2, End>:
  match dl:
    case None{}:
      go(xs, Open{None{}})
    case Some{d}:
      match d:
        case 0n:
          [Expired{}]
        case 1n+m:
          go(xs, Open{Some{m}})

# What the laws speak of
# ----------------------

def has_arrive(xs: List<&2, Sig>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case s <> rest:
      match s:
        case Arrive{}:
          True{}
        case Tick{}:
          has_arrive(rest)
        case Cancel{}:
          has_arrive(rest)

def has_cancel(xs: List<&2, Sig>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case s <> rest:
      match s:
        case Arrive{}:
          has_cancel(rest)
        case Tick{}:
          has_cancel(rest)
        case Cancel{}:
          True{}

def ticks(xs: List<&2, Sig>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case s <> rest:
      match s:
        case Arrive{}:
          ticks(rest)
        case Tick{}:
          1n+ticks(rest)
        case Cancel{}:
          ticks(rest)

# k ticks reach the deadline dl
def reached(dl: Maybe<&2, Nat>, k: Nat) -> Bool:
  match dl:
    case None{}:
      False{}
    case Some{d}:
      Nat.is_le(d, k)

# xs holds a cancel, or ticks enough to pass the deadline
def stops(+dl: Maybe<&2, Nat>, +xs: List<&2, Sig>) -> Bool:
  Bool.or(has_cancel(xs), reached(dl, ticks(xs)))

# xs holds something that ends the wait: the event, a cancel, the deadline
def exits(+dl: Maybe<&2, Nat>, +xs: List<&2, Sig>) -> Bool:
  Bool.or(has_arrive(xs), stops(dl, xs))

# how many ends a wait reports when b says whether something ends it
def once(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n
