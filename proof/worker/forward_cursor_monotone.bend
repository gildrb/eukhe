# eukhe: the proof of LAW forward_cursor_monotone
#
# PROOF of LAW forward_cursor_monotone: the cursor is the spec's
# (forward_cursor_exact), the largest of the old cursor and some seqs:
# never below the old cursor (wb_cursor_ge, from Base's Nat.max_ge_l).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker
import ./forward_cursor_exact.bend as PWorkerForwardCursorExact

def Worker.forward_cursor_monotone(c, ms, note):
  +ps = Worker.fw_seqs(Worker.fw_new(c, ms))
  %Equal.sym(Nat, Worker.fw_cursor_of(Wk.pick(c, ms, note)), Worker.fw_cursor(ps, c), Worker.forward_cursor_exact(c, ms, note)) : {Nat.is_le(c, _) == True{} : Bool}
  LAWorker.wb_cursor_ge(ps, c)
