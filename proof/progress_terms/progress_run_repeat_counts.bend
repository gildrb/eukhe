# eukhe: the proof of LAW progress_run_repeat_counts
#
# PROOF: acts the session did keep its work (pgt.no_growth), so the check
# strikes one more stall, below twice the cap and not the cap.

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ../base/nat.bend as LNat
import ./base.bend as LPT

def ProgressTerms.progress_run_repeat_counts(cap, s, hist, seg, segs, within, below, other):
  %Equal.sym(Bool, Pr.grew(hist, seg), False{}, LPT.pgt.no_growth(hist, seg, within)) : {Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, _)) == Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{1n+s}) : Pr.Run}
  %Equal.sym(Bool, Nat.is_le(Nat.add(cap, cap), 1n+s), False{}, LNat.pc.lt_not_le(1n+s, Nat.add(cap, cap), below)) : {Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.strike.put(_, Nat.is_eq(cap, 1n+s), 1n+s)) == Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{1n+s}) : Pr.Run}
  %Equal.sym(Bool, Nat.is_eq(cap, 1n+s), False{}, other) : {Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.strike.put(False{}, _, 1n+s)) == Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{1n+s}) : Pr.Run}
  {==}
