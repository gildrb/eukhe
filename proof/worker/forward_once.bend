# eukhe: the proof of LAW forward_once
#
# PROOF of LAW forward_once: every seq the first pick hands on is at most
# its new cursor b (wb_top_bound); every seq the second pick hands on is
# past b (wb_new_gt); so none is both (wb_disjoint).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker/forward.bend as WorkerForward
import ./base.bend as LAWorker

def WorkerForward.forward_once(c, ms, note, ms2, note2):
  +sel = Wk.after(c, ms)
  +b = Wk.top(sel, c)
  +ps = Wk.seqs(sel)
  LAWorker.wb_disjoint(ps, b, Wk.seqs(Wk.after(b, ms2)),
    LAWorker.wb_and_r(Nat.is_le(c, b), WorkerForward.fw_all_le(ps, b), LAWorker.wb_top_bound(sel, c)),
    LAWorker.wb_new_gt(b, ms2))
