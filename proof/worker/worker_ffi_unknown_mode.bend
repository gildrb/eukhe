# eukhe: the proof of LAW worker_ffi_unknown_mode
#
# PROOF of LAW worker_ffi_unknown_mode: after the step tag, the mode tag
# 2 + n reads as itself or as Bad (ws_nat_read); both ways the mode is Bad
# (wu_mode), so the state reader reads Bad (wum_st) and the request is
# malformed.

import Base
import ../../bend/worker.bend as Wk
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base/unknown.bend as LAWorkerUnknown

# a state whose mode tag is past 1 reads as no state
def wum_st(+n: Nat, +rest: String) -> {FWk.get_st(Wr.put_nat(2n+n, rest)) == Wr.Bad{} : Wr.Dec<Wk.St>}:
  +a = LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), a, LAWireSpell.ws_nat_read(2n+n, rest)) : {FWk.get_st.mode(FWk.get_mode.go(_)) == Wr.Bad{} : Wr.Dec<Wk.St>}
  %Equal.sym(Wr.Dec<Wk.Mode>, FWk.get_mode.go(a), Wr.Bad{}, LAWorkerUnknown.wu_mode(LawsBase.wire_fits(2n+n), n, rest)) : {FWk.get_st.mode(_) == Wr.Bad{} : Wr.Dec<Wk.St>}
  {==}

def Worker.worker_ffi_unknown_mode(n, rest):
  %Equal.sym(Wr.Dec<Wk.St>, FWk.get_st(Wr.put_nat(2n+n, rest)), Wr.Bad{}, wum_st(n, rest)) : {FWk.ffi.go(FWk.get_req.st(_)) == Wr.err("worker: malformed request") : String}
  {==}
