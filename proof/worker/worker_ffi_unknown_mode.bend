# eukhe: the proof of LAW worker_ffi_unknown_mode
#
# PROOF of LAW worker_ffi_unknown_mode: after the step tag, the state reader
# reads Bad (worker_ffi_unknown_reply_mode), so the request is malformed.

import Base
import ../../bend/worker.bend as Wk
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/worker.bend as Worker
import ./worker_ffi_unknown_reply_mode.bend as PWorkerUnknownReplyMode

def Worker.worker_ffi_unknown_mode(n, rest):
  %Equal.sym(Wr.Dec<Wk.St>, FWk.get_st(Wr.put_nat(2n+n, rest)), Wr.Bad{}, Worker.worker_ffi_unknown_reply_mode(n, rest)) : {FWk.ffi.go(FWk.get_req.st(_)) == Wr.err("worker: malformed request") : String}
  {==}
