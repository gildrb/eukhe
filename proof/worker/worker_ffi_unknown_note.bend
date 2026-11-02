# eukhe: the proof of LAW worker_ffi_unknown_note
#
# PROOF of LAW worker_ffi_unknown_note: the cursor and the messages read
# back (wr_nat, wr_umsgs); the note tag 2 + n reads as itself or as Bad
# (ws_nat_read); both ways the note is Bad (wu_note), so the request is
# malformed.

import Base
import ../../bend/worker.bend as Wk
import ../../bend/ffi_worker.bend as FWk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/worker.bend as Worker
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LAWorker
import ./base/entry.bend as LAWorkerEntry
import ./base/unknown.bend as LAWorkerUnknown

def Worker.worker_ffi_unknown_note(c, ms, n, rest, h):
  +hh = h
  +x = Wr.put_nat(2n+n, rest)
  +y = Worker.wk_spell_umsgs(ms, x)
  +a = LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest)
  %LAWorkerEntry.wr_nat(c, y, LAWorker.wb_and_l(LawsBase.wire_fits(c), Worker.wk_umsgs_fit(ms), hh)) : {FWk.ffi.go(FWk.get_req.cursor(_)) == Wr.err("worker: malformed request") : String}
  %Equal.sym(Wr.Dec<List<&2, Wk.UMsg>>, FWk.get_umsgs(y), Wr.Got{ms, x}, LAWorkerEntry.wr_umsgs(ms, x, LAWorker.wb_and_r(LawsBase.wire_fits(c), Worker.wk_umsgs_fit(ms), hh))) : {FWk.ffi.go(FWk.get_req.msgs(c, _)) == Wr.err("worker: malformed request") : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), a, LAWireSpell.ws_nat_read(2n+n, rest)) : {FWk.ffi.go(FWk.get_req.note(c, ms, FWk.get_note.go(_))) == Wr.err("worker: malformed request") : String}
  %Equal.sym(Wr.Dec<Maybe<&2, String>>, FWk.get_note.go(a), Wr.Bad{}, LAWorkerUnknown.wu_note(LawsBase.wire_fits(2n+n), n, rest)) : {FWk.ffi.go(FWk.get_req.note(c, ms, _)) == Wr.err("worker: malformed request") : String}
  {==}
