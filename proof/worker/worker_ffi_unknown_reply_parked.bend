# eukhe: the proof of LAW worker_ffi_unknown_reply_parked
#
# PROOF of LAW worker_ffi_unknown_reply_parked: the mode reads back
# (wr_mode); the parked tag 2 + n reads as itself or as Bad (ws_nat_read);
# both ways the parked boundary is Bad (wu_parked), so the state is.

import Base
import ../../bend/worker.bend as Wk
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LAWorkerEntry
import ./base/unknown.bend as LAWorkerUnknown

def Worker.worker_ffi_unknown_reply_parked(m, n, rest):
  +x = Wr.put_nat(2n+n, rest)
  +a = LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)
  %Equal.sym(Wr.Dec<Wk.Mode>, FWk.get_mode(Worker.wk_spell_mode(m, x)), Wr.Got{m, x}, LAWorkerEntry.wr_mode(m, x)) : {FWk.get_st.mode(_) == Wr.Bad{} : Wr.Dec<Wk.St>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), a, LAWireSpell.ws_nat_read(2n+n, rest)) : {FWk.get_st.parked(m, FWk.get_parked.go(_)) == Wr.Bad{} : Wr.Dec<Wk.St>}
  %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FWk.get_parked.go(a), Wr.Bad{}, LAWorkerUnknown.wu_parked(LawsBase.wire_fits(2n+n), n, rest)) : {FWk.get_st.parked(m, _) == Wr.Bad{} : Wr.Dec<Wk.St>}
  {==}
