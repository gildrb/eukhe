# eukhe: the proof of LAW goal_compared_check

import Base
import ../../laws/progress.bend as Progress
import ../../bend/progress.bend as Pr

def gcc.same(b: Bool, +t: Nat, +cap: Nat, +s: Nat, +w: Nat, +work: Nat) -> {Pr.judge(t, cap, Pr.compared.of(b, s, w), work) == Progress.gc_same(b, t, cap, s, w, work) : Pr.Goal}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Progress.goal_compared_check(t, cap, m, work):
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Pr.Last{r, g, s, w}:
          gcc.same(Bool.and(r, g), t, cap, s, w, work)
