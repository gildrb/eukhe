# eukhe: the proof of LAW forward_verbatim
#
# PROOF of LAW forward_verbatim: the pick's text is the model's body of
# the model's messages past the cursor, which are the spec's (wb_after);
# the body is Base's join of their texts, then the note (wb_body).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker/forward.bend as WorkerForward
import ./base.bend as LAWorker

def WorkerForward.forward_verbatim(c, ms, note):
  %Equal.sym(List<&2, Wk.UMsg>, Wk.after(c, ms), WorkerForward.fw_new(c, ms), LAWorker.wb_after(c, ms)) : {Wk.body(_, note) == WorkerForward.fw_body(WorkerForward.fw_texts(WorkerForward.fw_new(c, ms)), note) : String}
  LAWorker.wb_body(WorkerForward.fw_new(c, ms), note)
