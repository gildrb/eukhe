# eukhe: the proof of LAW progress_within_exact
#
# PROOF: by unfolding for no act and one act; by induction on the first run
# for two (pgt.within_split, pgt.within_join).

import Base
import ../../bend/progress.bend as Pr
import ../../bend/child.bend as Ch
import ../../laws/progress_terms.bend as ProgressTerms
import ./base.bend as LPT

def pgt.within_one(+x: Nat, +s: List<&2, Nat>, w: Pr.Within([x], s)) -> Pr.In(x, s):
  (i, u) = w
  i

def pgt.within_both(a: List<&2, Nat>, +b: List<&2, Nat>, +s: List<&2, Nat>, ab: Pr.Within(a, s) & Pr.Within(b, s)) -> Pr.Within(List.append(&2, Nat, a, b), s):
  (wa, wb) = ab
  LPT.pgt.within_join(a, b, s, wa, wb)

def ProgressTerms.progress_within_exact(x, a, b, s):
  (Unit{}, ((w => pgt.within_one(x, s, w), i => (i, Unit{})), (w => LPT.pgt.within_split(a, b, s, w), ab => pgt.within_both(a, b, s, ab))))
