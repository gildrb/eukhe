# eukhe: the proof of LAW retry_note_ffi_left_over

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

# PROOF of LAW retry_note_ffi_left_over: the request reads back with the rest untouched (rn.reads); the rest is not empty, so the entry answers the left-over error form.

def RetryNote.retry_note_ffi_left_over(q, h, t, fit):
  match q:
    case FRn.Req{+a, +c}:
      %Equal.sym(String, FRn.ffi(RetryNote.spell_req(FRn.Req{a, c}, SCon{h, t})), FRn.ffi.done(FRn.Req{a, c}, Wr.end(SCon{h, t})), LARetryNote.rn.reads(FRn.Req{a, c}, SCon{h, t}, fit)) : {_ == Wr.err("retry_note: input left after the request") : String}
      {==}
