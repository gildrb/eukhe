# agents (spec): whether a run goes on past a final answer that leaves
# task work undone (spec/README.md A4), stated without the rule of
# bend/work_left.bend, and the wire of its entry (bend/ffi_work_left.bend,
# crates/eukhe-bend/WIRE.md). The laws of area work_left state K1-K8 one
# property at a time, with the helpers below. A spec: the shipped code
# never calls it.
#
# K1: a final answer is the run's to judge exactly when nothing else owns
#     the boundary and the run may go on: no autonomous run or loop drives
#     it, no input is queued (user input, unsettled children or workflow
#     runs), the run acted since the user's last message (a tool call with
#     an effect), the session's budget admits more work, the progress
#     check (bend/progress.bend `judge`: directors.stallSteps continuations
#     in a row with no new tool result stop it) goes on, and the Director
#     loop has a step left. The check's steer goes on; Rust sends it as a
#     stop (K6).
# K2: an answer the run judges that the judge did not read yet: the core
#     asks for the reading (one model request, no tools, the answer alone).
# K3: an answer the run judges that the judge read as stating work left:
#     the run goes on with one harness continuation.
# K4: every other answer stands and the run yields: one that states no
#     work left, one the judge gave no verdict on (an unjudged answer never
#     continues), and every answer K1 does not judge.
# K5: a continuation costs exactly one step of the Director loop.
# K6: a request is four Bools: driven, queued, acted, funded, then the
#     progress check: 0 go | 1 stop, each with its count of stalls (Nat),
#     the loop's steps left (Nat), then the reading: 0 not read | 1 no
#     work left | 2 work left | 3 no verdict. The check's steer (2) is no
#     request: Rust sends a steer as a stop.
# K7: a reply is 0 continue, with the steps left after it (Nat) | 1 yield
#     | 2 ask the judge.
# K8: anything else is no request: the entry answers it with exactly
#     `E work_left: malformed request`.

import Base
import ../../bend/progress.bend as Pg
import ../../bend/work_left.bend as Wl
import ../../bend/wire.bend as Wr

# The step (K1-K5)
# ----------------

# K1: the progress check stopped
def stopped(s: Pg.Run) -> Bool:
  match s:
    case Pg.Go{k}:
      False{}
    case Pg.Stop{k}:
      True{}
    case Pg.Steer{k}:
      False{}

# K1: the loop has no step left
def no_step(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      False{}

# K1: something keeps the run from going on: a driver drives it, input is
# queued, it did not act, the budget admits no more work, the progress
# check stopped, or the loop has no step left
def kept(f: Wl.Facts) -> Bool:
  match f:
    case Wl.Facts{d, q, a, b, s, n, r}:
      Bool.or(d, Bool.or(q, Bool.or(Bool.not(a), Bool.or(Bool.not(b), Bool.or(stopped(s), no_step(n))))))

# K1: the answer is the run's to judge
def judged(+f: Wl.Facts) -> Bool:
  Bool.not(kept(f))

# the judge's reading of the facts
def reading_of(f: Wl.Facts) -> Wl.Reading:
  match f:
    case Wl.Facts{d, q, a, b, s, n, r}:
      r

# the loop's steps left
def left_of(f: Wl.Facts) -> Nat:
  match f:
    case Wl.Facts{d, q, a, b, s, n, r}:
      n

# K3: the reading states work left
def reading_left(r: Wl.Reading) -> Bool:
  match r:
    case Wl.Unread{}:
      False{}
    case Wl.Finished{}:
      False{}
    case Wl.Left{}:
      True{}
    case Wl.Unjudged{}:
      False{}

# K2: the judge has not read the answer
def reading_unread(r: Wl.Reading) -> Bool:
  match r:
    case Wl.Unread{}:
      True{}
    case Wl.Finished{}:
      False{}
    case Wl.Left{}:
      False{}
    case Wl.Unjudged{}:
      False{}

# K3: the run goes on
def continue_due(+f: Wl.Facts) -> Bool:
  Bool.and(judged(f), reading_left(reading_of(f)))

# K2: the core asks for the reading
def ask_due(+f: Wl.Facts) -> Bool:
  Bool.and(judged(f), reading_unread(reading_of(f)))

# whether a step goes on
def continues(s: Wl.Step) -> Bool:
  match s:
    case Wl.Continue{m}:
      True{}
    case Wl.Yield{}:
      False{}
    case Wl.Ask{}:
      False{}

# whether a step asks for the judge's reading
def asks(s: Wl.Step) -> Bool:
  match s:
    case Wl.Continue{m}:
      False{}
    case Wl.Yield{}:
      False{}
    case Wl.Ask{}:
      True{}

# K5: the loop's steps before a step of f: a continuation's steps after it
# and the one it spent; a step that does not go on spends none
def steps_before(+f: Wl.Facts, s: Wl.Step) -> Nat:
  match s:
    case Wl.Continue{m}:
      1n+m
    case Wl.Yield{}:
      left_of(f)
    case Wl.Ask{}:
      left_of(f)

# Requests and replies (K6-K7)
# ----------------------------

def w_stall(s: Pg.Run, rest: String) -> String:
  match s:
    case Pg.Go{k}:
      Wr.put_nat(0n, Wr.put_nat(k, rest))
    case Pg.Stop{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))
    case Pg.Steer{k}:
      Wr.put_nat(2n, Wr.put_nat(k, rest))

def w_reading(r: Wl.Reading, rest: String) -> String:
  match r:
    case Wl.Unread{}:
      Wr.put_nat(0n, rest)
    case Wl.Finished{}:
      Wr.put_nat(1n, rest)
    case Wl.Left{}:
      Wr.put_nat(2n, rest)
    case Wl.Unjudged{}:
      Wr.put_nat(3n, rest)

# a request, then rest
def w_req(f: Wl.Facts, rest: String) -> String:
  match f:
    case Wl.Facts{d, q, a, b, s, n, r}:
      Wr.put_bool(d, Wr.put_bool(q, Wr.put_bool(a, Wr.put_bool(b, w_stall(s, Wr.put_nat(n, w_reading(r, rest)))))))

# a reply, then rest
def w_step(s: Wl.Step, rest: String) -> String:
  match s:
    case Wl.Continue{m}:
      Wr.put_nat(0n, Wr.put_nat(m, rest))
    case Wl.Yield{}:
      Wr.put_nat(1n, rest)
    case Wl.Ask{}:
      Wr.put_nat(2n, rest)
