# eukhe: the proof of LAW worker_ffi_unknown_verdict
#
# PROOF of LAW worker_ffi_unknown_verdict: the tag 6 + n reads as itself or
# as Bad (ws_nat_read); both ways the verdict reader answers Bad (wu_verdict).

import Base
import ../../bend/worker.bend as Wk
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base/unknown.bend as LAWorkerUnknown

def Worker.worker_ffi_unknown_verdict(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(6n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest), LAWireSpell.ws_nat_read(6n+n, rest)) : {FWk.get_verdict.go(_) == Wr.Bad{} : Wr.Dec<Wk.Verdict>}
  LAWorkerUnknown.wu_verdict(LawsBase.wire_fits(6n+n), n, rest)
