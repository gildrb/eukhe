# eukhe: the laws of area progress (the model's terms, pinned)
#
# The model laws of laws/progress.bend (child_*, goal_*) state the work
# ledger, the goal loop and the child watch through the model's own terms
# (`mem`, `In`, `Within`, `Repeats`, `Loops`, `goal`, `watch`,
# `Goal.stalls`). Fresh adversaries (SpecCheckProgress, SpecCheckProgress3)
# noted that no law pinned them, so a model with `In = Empty` passes five
# of those laws vacuously. Each term is pinned here to a spec in the laws
# (the type terms both ways).

import Base
import ../bend/progress.bend as Pr
import ../bend/child.bend as Ch

# x is one of xs
def mem_spec(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), mem_spec(x, t))

# every act of xs is one of s
def within_spec(xs: List<&2, Nat>, +s: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(mem_spec(h, s), within_spec(t, s))

# every segment holds only acts of hist
def repeats_spec(segs: List<&2, List<&2, Nat>>, +hist: List<&2, Nat>) -> Bool:
  match segs:
    case Nil{}:
      True{}
    case seg <> rest:
      Bool.and(within_spec(seg, hist), repeats_spec(rest, hist))

# every poll shows only acts of hist
def loops_spec(ps: List<&2, Pr.Peek>, +hist: List<&2, Nat>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> rest:
      match p:
        case Pr.Peek{seg, dt}:
          Bool.and(within_spec(seg, hist), loops_spec(rest, hist))

def stalls_spec(g: Pr.Goal) -> Nat:
  match g:
    case Pr.Go{s}:
      s
    case Pr.Stop{s}:
      s

# the goal loop: a check at each continuation on the acts so far; a
# stopped goal stays stopped
def goal_spec(segs: List<&2, List<&2, Nat>>, +cap: Nat, +hist: List<&2, Nat>, g: Pr.Goal) -> Pr.Goal:
  match segs:
    case Nil{}:
      g
    case +seg <> rest:
      match g:
        case Pr.Go{s}:
          goal_spec(rest, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, Pr.grew(hist, seg)))
        case Pr.Stop{s}:
          Pr.Stop{s}

def watch_spec.at(+cfg: Ch.Cfg, t: Nat, +dt: Nat, x: Ch.Next) -> Ch.Next:
  match x:
    case Ch.Watch{w}:
      Ch.look(cfg, w, 1n+dt, Ch.Busy{Some{t}})
    case Ch.Owe{k}:
      Ch.Owe{k}
    case Ch.Quiet{}:
      Ch.Quiet{}

# the watch: at each poll, a watching verdict looks again with the work so
# far and one more interval; a verdict that owes or is quiet stays
def watch_spec(ps: List<&2, Pr.Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, x: Ch.Next) -> Ch.Next:
  match ps:
    case Nil{}:
      x
    case p <> rest:
      match p:
        case Pr.Peek{+seg, +dt}:
          watch_spec(rest, cfg, List.append(&2, Nat, hist, seg), watch_spec.at(cfg, Pr.work(List.append(&2, Nat, hist, seg)), dt, x))

# LAW progress_terms_exact: the model's membership, the stall count of a verdict, the goal loop
# and the child watch are what the progress laws read them as
# EXCLUDES: terms that make the goal and child laws vacuous or say less than their names
law progress_terms_exact:
  for +x: Nat
  for +xs: List<&2, Nat>
  for +g: Pr.Goal
  for +segs: List<&2, List<&2, Nat>>
  for +cap: Nat
  for +hist: List<&2, Nat>
  for +ps: List<&2, Pr.Peek>
  for +cfg: Ch.Cfg
  for +v: Ch.Next
  {Pr.mem(x, xs) == mem_spec(x, xs) : Bool} & {Pr.Goal.stalls(g) == stalls_spec(g) : Nat} & {Pr.goal(segs, cap, hist, g) == goal_spec(segs, cap, hist, g) : Pr.Goal} & {Pr.watch(ps, cfg, hist, v) == watch_spec(ps, cfg, hist, v) : Ch.Next}

# LAW progress_type_terms_exact: the model's type terms hold exactly when their Bools in the laws
# are true: x is one of xs; every act of xs is one of s; every segment holds only acts of hist;
# every poll shows only acts of hist
# EXCLUDES: an `In` that never holds or a `Within`, `Repeats` or `Loops` that always holds (the
#   child and goal laws vacuous)
law progress_type_terms_exact:
  for +x: Nat
  for +xs: List<&2, Nat>
  for +s: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for +ps: List<&2, Pr.Peek>
  ((Pr.In(x, xs) -> {mem_spec(x, xs) == True{} : Bool}) & ({mem_spec(x, xs) == True{} : Bool} -> Pr.In(x, xs))) & ((Pr.Within(xs, s) -> {within_spec(xs, s) == True{} : Bool}) & ({within_spec(xs, s) == True{} : Bool} -> Pr.Within(xs, s))) & ((Pr.Repeats(segs, s) -> {repeats_spec(segs, s) == True{} : Bool}) & ({repeats_spec(segs, s) == True{} : Bool} -> Pr.Repeats(segs, s))) & ((Pr.Loops(ps, s) -> {loops_spec(ps, s) == True{} : Bool}) & ({loops_spec(ps, s) == True{} : Bool} -> Pr.Loops(ps, s)))
