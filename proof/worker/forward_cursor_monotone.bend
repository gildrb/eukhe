# eukhe: the proof of LAW forward_cursor_monotone
#
# PROOF of LAW forward_cursor_monotone: the old cursor is at most the new
# one, the first fact of wb_top_bound (the new cursor is Base's Nat.max of
# the old cursor and the seqs handed on).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker/forward.bend as WorkerForward
import ./base.bend as LAWorker

def WorkerForward.forward_cursor_monotone(c, ms, note):
  +sel = Wk.after(c, ms)
  LAWorker.wb_and_l(Nat.is_le(c, Wk.top(sel, c)), WorkerForward.fw_all_le(Wk.seqs(sel), Wk.top(sel, c)), LAWorker.wb_top_bound(sel, c))
