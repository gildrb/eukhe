# eukhe: the proof of LAW worker_ffi_spelled_left_over
#
# PROOF of LAW worker_ffi_spelled_left_over: the decoder reads the spelled
# request and leaves the rest (we_spelled); a rest that is not empty is
# refused.

import Base
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/worker.bend as Worker
import ./base/entry.bend as LAWorkerEntry

def wlo_whole(-r: FWk.Req, +rest: String, more: {String.is_empty(rest) == False{} : Bool}) -> {FWk.ffi.whole(r, Wr.end(rest)) == Wr.err("worker: input left over") : String}:
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FWk.ffi.whole(r, _) == Wr.err("worker: input left over") : String}
  {==}

def Worker.worker_ffi_spelled_left_over(r, rest, h, more):
  Equal.trans(String, FWk.ffi(Worker.wk_spell_req(r, rest)), FWk.ffi.whole(r, Wr.end(rest)), Wr.err("worker: input left over"),
    LAWorkerEntry.we_spelled(r, rest, h), wlo_whole(r, rest, more))
