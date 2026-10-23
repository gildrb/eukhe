# eukhe: the proof of LAW goal_progress_continues

import Base
import ../../bend/progress.bend as Pr
import ../../LAWS.bend as Laws
import ./base.bend as LA

# new work clears the count
def pp.grew_yes(+cap: Nat, +s: Nat, +hist: List<&2, Nat>, +seg: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, hist) == False{} : Bool}, i: Pr.In(x, seg)) -> {Pr.check(cap, s, Pr.grew(hist, seg)) == Pr.Go{0n} : Pr.Goal}:
  %Equal.sym(Bool, Pr.grew(hist, seg), True{}, LA.pp.new_work(hist, seg, x, fresh, i)) : {Pr.check(cap, s, _) == Pr.Go{0n} : Pr.Goal}
  {==}

def Laws.goal_progress_continues(cap, s, hist, seg, x, fresh, news):
  pp.grew_yes(cap, s, hist, seg, x, fresh, news)
