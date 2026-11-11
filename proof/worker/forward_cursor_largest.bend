# eukhe: the proof of LAW forward_cursor_largest
#
# PROOF of LAW forward_cursor_largest: the new cursor is the model's top of
# the messages past the cursor; it is Base's Nat.max of the old cursor and
# their seqs, so neither the old cursor nor any seq is above it
# (wb_top_bound); and each step of top keeps either the cursor so far or
# the seq it meets, so the result is one of them (wb_top_in).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker/forward.bend as WorkerForward
import ./base.bend as LAWorker

def WorkerForward.forward_cursor_largest(c, ms, note):
  +sel = Wk.after(c, ms)
  LAWorker.wb_and_tt(WorkerForward.fw_all_le(c <> Wk.seqs(sel), Wk.top(sel, c)), WorkerForward.fw_in(Wk.top(sel, c), c <> Wk.seqs(sel)), LAWorker.wb_top_bound(sel, c), LAWorker.wb_top_in(sel, c))
