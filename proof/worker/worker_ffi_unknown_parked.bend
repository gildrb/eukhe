# eukhe: the proof of LAW worker_ffi_unknown_parked
#
# PROOF of LAW worker_ffi_unknown_parked: after the step tag, the state
# reader reads Bad (worker_ffi_unknown_reply_parked), so the request is
# malformed.

import Base
import ../../bend/worker.bend as Wk
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/worker.bend as Worker
import ./worker_ffi_unknown_reply_parked.bend as PWorkerUnknownReplyParked

def Worker.worker_ffi_unknown_parked(m, n, rest):
  %Equal.sym(Wr.Dec<Wk.St>, FWk.get_st(Worker.wk_spell_mode(m, Wr.put_nat(2n+n, rest))), Wr.Bad{}, Worker.worker_ffi_unknown_reply_parked(m, n, rest)) : {FWk.ffi.go(FWk.get_req.st(_)) == Wr.err("worker: malformed request") : String}
  {==}
