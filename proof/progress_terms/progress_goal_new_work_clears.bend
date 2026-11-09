# eukhe: the proof of LAW progress_goal_new_work_clears
#
# PROOF: an act the session never did grows its work (pp.new_work of
# proof/progress/base.bend), so the check clears the count.

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT
import ../progress/base.bend as LA

def ProgressTerms.progress_goal_new_work_clears(cap, s, hist, seg, segs, x, fresh, news):
  %Equal.sym(Bool, Pr.grew(hist, seg), True{}, LA.pp.new_work(hist, seg, x, fresh, news)) : {Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, _)) == Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{0n}) : Pr.Goal}
  {==}
