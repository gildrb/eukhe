# eukhe: the proof of LAW forward_cursor_exact
#
# PROOF of LAW forward_cursor_exact: the pick's cursor is the model's top of
# the model's messages past the cursor, which are the spec's (wb_after);
# top folds higher, which is Base's Nat.max (wb_top).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.forward_cursor_exact(c, ms, note):
  %Equal.sym(List<&2, Wk.UMsg>, Wk.after(c, ms), Worker.fw_new(c, ms), LAWorker.wb_after(c, ms)) : {Wk.top(_, c) == Worker.fw_cursor(Worker.fw_seqs(Worker.fw_new(c, ms)), c) : Nat}
  LAWorker.wb_top(Worker.fw_new(c, ms), c)
