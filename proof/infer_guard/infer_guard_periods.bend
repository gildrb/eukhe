# eukhe: the proof of LAW infer_guard_periods
#
# PROOF: 4(1 + q) <= k < 4(2 + q) makes k/4 = 1 + q (LAGuard.gb.quarter_at,
# by induction on q, four chunks of the window at a time); a quarter of
# at least 1 is the longest period.

import Base
import ../../bend/infer.bend as If
import ../../laws/infer_guard.bend as InferGuard
import ./base.bend as LAGuard

def InferGuard.infer_guard_periods(k, q, lo, hi):
  %Equal.sym(Nat, If.quarter(k), 1n+q, LAGuard.gb.quarter_at(1n+q, k, lo, hi)) : {If.periods.of(_) == 1n+q : Nat}
  {==}
