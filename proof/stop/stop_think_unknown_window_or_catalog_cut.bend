# eukhe: the proof of LAW stop_think_unknown_window_or_catalog_cut
#
# PROOF: an unknown window passes the window test at once, so a stop that can compact compacts; with a known window, an output at or past the catalog cap fails it (LR.str.bound_cut); a failed window test is no compaction (LR.str.no_shrink).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_think_unknown_window_or_catalog_cut(rc, w, c, p, o, x, lower, k, row):
  ({==}, LR.str.no_shrink(rc, 1n+w, c, p, Nat.add(c, x), lower, k, row, LR.str.bound_cut(w, c, p, x)))
