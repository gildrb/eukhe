# eukhe: the proof of LAW progress_run_repeat_steers
#
# PROOF: acts the session did keep its work (pgt.no_growth), so the check
# strikes one more stall: the cap, below twice the cap (pp.twice_not_le).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ../base/nat.bend as LNat
import ../progress/base.bend as LA
import ./base.bend as LPT

def ProgressTerms.progress_run_repeat_steers(s, hist, seg, segs, within):
  %Equal.sym(Bool, Pr.grew(hist, seg), False{}, LPT.pgt.no_growth(hist, seg, within)) : {Pr.run(segs, 1n+s, List.append(&2, Nat, hist, seg), Pr.check(1n+s, s, _)) == Pr.run(segs, 1n+s, List.append(&2, Nat, hist, seg), Pr.Steer{1n+s}) : Pr.Run}
  %Equal.sym(Bool, Nat.is_le(Nat.add(1n+s, 1n+s), 1n+s), False{}, LA.pp.twice_not_le(s)) : {Pr.run(segs, 1n+s, List.append(&2, Nat, hist, seg), Pr.strike.put(_, Nat.is_eq(1n+s, 1n+s), 1n+s)) == Pr.run(segs, 1n+s, List.append(&2, Nat, hist, seg), Pr.Steer{1n+s}) : Pr.Run}
  %Equal.sym(Bool, Nat.is_eq(1n+s, 1n+s), True{}, LNat.child.pc.eq_refl(1n+s)) : {Pr.run(segs, 1n+s, List.append(&2, Nat, hist, seg), Pr.strike.put(False{}, _, 1n+s)) == Pr.run(segs, 1n+s, List.append(&2, Nat, hist, seg), Pr.Steer{1n+s}) : Pr.Run}
  {==}
