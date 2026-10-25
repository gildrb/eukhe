# eukhe: the proof of LAW worker_ffi_unknown_ev
#
# PROOF of LAW worker_ffi_unknown_ev: the state reads back (wr_st); the
# event tag 6 + n reads as itself or as Bad (ws_nat_read); both ways the
# event is Bad (wu_ev), so the request is malformed.

import Base
import ../../bend/worker.bend as Wk
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LAWorkerEntry
import ./base/unknown.bend as LAWorkerUnknown

def Worker.worker_ffi_unknown_ev(s, n, rest, h):
  +x = Wr.put_nat(6n+n, rest)
  +a = LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest)
  %Equal.sym(Wr.Dec<Wk.St>, FWk.get_st(Worker.wk_spell_st(s, x)), Wr.Got{s, x}, LAWorkerEntry.wr_st(s, x, h)) : {FWk.ffi.go(FWk.get_req.st(_)) == Wr.err("worker: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), a, LAWireSpell.ws_nat_read(6n+n, rest)) : {FWk.ffi.go(FWk.get_req.ev(s, FWk.get_ev.go(_))) == Wr.err("worker: malformed request") : String}
  %Equal.sym(Wr.Dec<Wk.Ev>, FWk.get_ev.go(a), Wr.Bad{}, LAWorkerUnknown.wu_ev(LawsBase.wire_fits(6n+n), n, rest)) : {FWk.ffi.go(FWk.get_req.ev(s, _)) == Wr.err("worker: malformed request") : String}
  {==}
