# eukhe: the proof of LAW progress_goal_repeat_counts
#
# PROOF: acts the session did keep its work (pgt.no_growth), so the check
# strikes one more stall, below the cap.

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_goal_repeat_counts(cap, s, hist, seg, segs, within, below):
  %Equal.sym(Bool, Pr.grew(hist, seg), False{}, LPT.pgt.no_growth(hist, seg, within)) : {Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, _)) == Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{1n+s}) : Pr.Goal}
  %Equal.sym(Bool, Nat.is_le(cap, 1n+s), False{}, below) : {Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.strike.put(_, 1n+s)) == Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{1n+s}) : Pr.Goal}
  {==}
