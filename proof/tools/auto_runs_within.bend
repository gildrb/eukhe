# eukhe: the proof of LAW auto_runs_within

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# The gate reads within
# ---------------------

def ps.auto_runs_within(+s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, ans: List<&2, Bool>, w: {Tl.within(Tl.Step.effs(s), auto) == True{} : Bool}) -> {Tl.exec(s <> post, auto, ans) == Tl.ran.add(s, Tl.exec(post, auto, ans)) : Tl.Ran}:
  %Equal.sym(Bool, Tl.within(Tl.Step.effs(s), auto), True{}, w) : {Tl.exec.go(s <> post, auto, _, ans) == Tl.ran.add(s, Tl.exec(post, auto, ans)) : Tl.Ran}
  {==}

def Tools.auto_runs_within(s, post, auto, ans, w):
  ps.auto_runs_within(s, post, auto, ans, w)
