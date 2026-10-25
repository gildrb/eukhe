# eukhe: the proof of LAW retry_note_ffi_answers

import Base
import ../../bend/retry_note.bend as Rn
import ../../bend/ffi_retry_note.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote
import ./retry_note_exact.bend as PRetryNoteExact

# PROOF of LAW retry_note_ffi_answers: the attempt and the cause read back with nothing left (rn.reads: rn.rt_cause, rn.list_rt over the wire round trips), and the model's note is the spec's (retry_note_exact).

def RetryNote.retry_note_ffi_answers(q, fit):
  match q:
    case FRn.Req{+a, +c}:
      %Equal.sym(String, FRn.ffi(RetryNote.spell_req(FRn.Req{a, c}, "")), FRn.ffi.done(FRn.Req{a, c}, Wr.end("")), LARetryNote.rn.reads(FRn.Req{a, c}, "", fit)) : {_ == Wr.put_str(RetryNote.note_spec(a, c), "") : String}
      %RetryNote.retry_note_exact(a, c) : {Wr.put_str(Rn.text(a, c), "") == Wr.put_str(_, "") : String}
      {==}
