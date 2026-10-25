# eukhe: the proof of LAW worker_ffi_unknown_req
#
# PROOF of LAW worker_ffi_unknown_req: the tag 2 + n reads as itself or as
# Bad (ws_nat_read); both ways the request is Bad (wu_req), so malformed.

import Base
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base/unknown.bend as LAWorkerUnknown

def Worker.worker_ffi_unknown_req(n, rest):
  +a = LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), a, LAWireSpell.ws_nat_read(2n+n, rest)) : {FWk.ffi.go(FWk.get_req.go(_)) == Wr.err("worker: malformed request") : String}
  %Equal.sym(Wr.Dec<FWk.Req>, FWk.get_req.go(a), Wr.Bad{}, LAWorkerUnknown.wu_req(LawsBase.wire_fits(2n+n), n, rest)) : {FWk.ffi.go(_) == Wr.err("worker: malformed request") : String}
  {==}
