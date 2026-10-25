# eukhe: the proof of LAW worker_ffi_decides
#
# PROOF of LAW worker_ffi_decides: the decoder reads the spelled request
# whole (we_spelled, from wr_req), so the entry runs the model on it, and
# its encoders spell the model's answer as the spec does (we_run).

import Base
import ../../bend/ffi_worker.bend as FWk
import ../../laws/worker.bend as Worker
import ./base/entry.bend as LAWorkerEntry

def Worker.worker_ffi_decides(r, h):
  Equal.trans(String, FWk.ffi(Worker.wk_spell_req(r, "")), FWk.ffi.run(r), Worker.wk_spell_reply(r), LAWorkerEntry.we_spelled(r, "", h), LAWorkerEntry.we_run(r))
