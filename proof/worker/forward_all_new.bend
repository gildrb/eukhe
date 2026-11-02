# eukhe: the proof of LAW forward_all_new
#
# PROOF of LAW forward_all_new: the pick's seqs are the model's seqs of the
# model's messages past the cursor; those are the spec's (wb_after,
# wb_seqs).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.forward_all_new(c, ms, note):
  %Equal.sym(List<&2, Wk.UMsg>, Wk.after(c, ms), Worker.fw_new(c, ms), LAWorker.wb_after(c, ms)) : {Wk.seqs(_) == Worker.fw_seqs(Worker.fw_new(c, ms)) : List<&2, Nat>}
  LAWorker.wb_seqs(Worker.fw_new(c, ms))
