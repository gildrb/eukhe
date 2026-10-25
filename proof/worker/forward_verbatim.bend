# eukhe: the proof of LAW forward_verbatim
#
# PROOF of LAW forward_verbatim: the pick's text is the model's body of
# the model's messages past the cursor, which are the spec's (wb_after);
# the body is Base's join of their texts, then the note (wb_body).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker.bend as Worker
import ./base.bend as LAWorker

def Worker.forward_verbatim(c, ms, note):
  %Equal.sym(List<&2, Wk.UMsg>, Wk.after(c, ms), Worker.fw_new(c, ms), LAWorker.wb_after(c, ms)) : {Wk.body(_, note) == Worker.fw_body(Worker.fw_texts(Worker.fw_new(c, ms)), note) : String}
  LAWorker.wb_body(Worker.fw_new(c, ms), note)
