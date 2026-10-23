# progress: what counts as progress when the harness checks a loop. The
# Rust code is the work ledger (crates/eukhe-core/src/durable/children/
# work.rs, `WorkLedger`), the goal's progress check (`stall_check` in
# crates/eukhe-core/src/durable/goals/state.rs, `goal_check` in
# goals/hooks.rs), and the subagent watch that reads the ledger's count
# as the child's progress token (crates/eukhe-daemon/src/worker/
# run_outcome.rs, with `look` in bend/child.bend).
#
# - An act is a fingerprint (a Nat): the Rust ledger hashes a tool call
#   with its result, or an accepted progress note. Two acts with the same
#   fingerprint are the same act.
# - The ledger keeps the distinct acts it read (`ledger`); the work is
#   their number (`work`).
# - The goal's progress check runs at each goal continuation: the work
#   grew since the last check, or not. New work clears the count of
#   continuations in a row with no new work; else the count grows by one,
#   and at the cap (directors.stallSteps) the goal stops (`check`).
#
# laws/progress.bend states what must hold; PROOF.bend proves it with
# proof/progress/. bridge/bridge_progress.bend runs `work` and
# `check` on the scenarios of the Rust bridge test.

import Base
import ./child.bend as Ch

# The ledger
# ----------

# x is one of the acts of s
def mem(+x: Nat, s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), mem(x, t))

def add.put(seen: Bool, x: Nat, s: List<&2, Nat>) -> List<&2, Nat>:
  match seen:
    case True{}:
      s
    case False{}:
      x <> s

# the acts of s, and x when it is new
def add(+s: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  add.put(mem(x, s), x, s)

# the distinct acts after reading xs, oldest first, on top of s
def ledger(xs: List<&2, Nat>, +s: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      s
    case +h <> t:
      ledger(t, add(s, h))

# the work of a session whose acts are xs: its distinct acts
def work(xs: List<&2, Nat>) -> Nat:
  List.length(&2, Nat, ledger(xs, Nil{}))

# x is an act of xs
def In(+x: Nat, xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case +h <> t:
      Or({x == h : Nat}, In(x, t))

# every act of xs is an act of s
def Within(xs: List<&2, Nat>, +s: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +h <> t:
      In(h, s) & Within(t, s)

# The goal's progress check
# -------------------------

# the check's verdict: continue with stalls continuations in a row that did
# no new work, or stop (the goal pauses) at that count
type Goal is Data:
  Go{stalls: Nat}
  Stop{stalls: Nat}

def strike.put(stop: Bool, n: Nat) -> Goal:
  match stop:
    case True{}:
      Stop{n}
    case False{}:
      Go{n}

# one more continuation with no new work after s of them
def strike(+cap: Nat, +s: Nat) -> Goal:
  strike.put(Nat.is_le(cap, 1n+s), 1n+s)

# the check at one continuation: the work grew since the last one, or not
def check(+cap: Nat, +s: Nat, grew: Bool) -> Goal:
  match grew:
    case True{}:
      Go{0n}
    case False{}:
      strike(cap, s)

# whether the work of hist ++ seg is more than the work of hist
def grew(+hist: List<&2, Nat>, seg: List<&2, Nat>) -> Bool:
  Nat.is_le(1n+work(hist), work(List.append(&2, Nat, hist, seg)))

# the goal loop: a check at each continuation, each one after the acts
# seg of the run since the last check, on the session's acts hist; a
# stopped goal stays stopped
def goal(segs: List<&2, List<&2, Nat>>, +cap: Nat, +hist: List<&2, Nat>, g: Goal) -> Goal:
  match segs:
    case Nil{}:
      g
    case +seg <> rest:
      match g:
        case Go{s}:
          goal(rest, cap, List.append(&2, Nat, hist, seg), check(cap, s, grew(hist, seg)))
        case Stop{s}:
          Stop{s}

def Goal.stopped(g: Goal) -> Bool:
  match g:
    case Go{s}:
      False{}
    case Stop{s}:
      True{}

# every segment of segs holds only acts of hist
def Repeats(segs: List<&2, List<&2, Nat>>, +hist: List<&2, Nat>) -> Type:
  match segs:
    case Nil{}:
      Unit
    case +seg <> rest:
      Within(seg, hist) & Repeats(rest, hist)

# The check the Rust goal loop runs
# ---------------------------------
# The Rust loop keeps, per run and goal, the count of stalls and the work
# (the ledger's count) at the last check, and compares counts: the work
# grew when its count did. The compiled core's wire carries a Nat up to
# 10^14 - 1, so the count is held below t = 10^14 - 1 and one more stall
# stays within t.

# the last check of the same run and goal: its count of stalls and the
# work then
type Prior is Data:
  Prior{stalls: Nat, work: Nat}

def Goal.stalls(g: Goal) -> Nat:
  match g:
    case Go{s}:
      s
    case Stop{s}:
      s

# the check at a continuation whose work is now `work`, after prior p
# (None: the first check of the run or the goal starts the count)
def judge(+t: Nat, +cap: Nat, p: Maybe<&2, Prior>, +work: Nat) -> Goal:
  match p:
    case None{}:
      Go{0n}
    case Some{x}:
      match x:
        case Prior{s, w}:
          check(cap, Nat.min(s, Nat.sub(t, 1n)), Nat.is_lt(w, work))

# The subagent watch
# ------------------
# The parent's watch polls the child; each poll reads the child unsettled
# with its progress token, the work of its acts so far, 1 + dt ms after the
# last poll.

type Peek is Data:
  Peek{seg: List<&2, Nat>, dt: Nat}

def watch.step(+cfg: Ch.Cfg, t: Nat, +dt: Nat, x: Ch.Next) -> Ch.Next:
  match x:
    case Ch.Watch{w}:
      Ch.look(cfg, w, 1n+dt, Ch.Busy{Some{t}})
    case Ch.Owe{k}:
      Ch.Owe{k}
    case Ch.Quiet{}:
      Ch.Quiet{}

# the watch's verdict after the polls ps, each after the acts seg the child
# did since the last poll, on the child's acts hist, from verdict x
def watch(ps: List<&2, Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, x: Ch.Next) -> Ch.Next:
  match ps:
    case Nil{}:
      x
    case p <> rest:
      match p:
        case Peek{+seg, +dt}:
          +now = List.append(&2, Nat, hist, seg)
          watch(rest, cfg, now, watch.step(cfg, work(now), dt, x))

# every poll of ps shows only acts of hist
def Loops(ps: List<&2, Peek>, +hist: List<&2, Nat>) -> Type:
  match ps:
    case Nil{}:
      Unit
    case p <> rest:
      match p:
        case Peek{seg, dt}:
          Within(seg, hist) & Loops(rest, hist)
