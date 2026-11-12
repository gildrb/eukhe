# eukhe: the proof of LAW progress_goal_repeat_stops
#
# PROOF: acts the session did keep its work (pgt.no_growth), so the check
# strikes one more stall, which reaches the cap; a stopped goal stays
# stopped (pgt.goal_stop).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def ProgressTerms.progress_goal_repeat_stops(cap, s, hist, seg, segs, within, reach):
  %Equal.sym(Bool, Pr.grew(hist, seg), False{}, LPT.pgt.no_growth(hist, seg, within)) : {Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, _)) == Pr.Stop{1n+s} : Pr.Goal}
  %Equal.sym(Bool, Nat.is_le(cap, 1n+s), True{}, reach) : {Pr.goal(segs, cap, List.append(&2, Nat, hist, seg), Pr.strike.put(_, 1n+s)) == Pr.Stop{1n+s} : Pr.Goal}
  LPT.pgt.goal_stop(segs, cap, List.append(&2, Nat, hist, seg), 1n+s)
