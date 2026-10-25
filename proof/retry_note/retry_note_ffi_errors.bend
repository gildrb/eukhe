# eukhe: the proof of LAW retry_note_ffi_errors

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

# PROOF of LAW retry_note_ffi_errors: the entry answers the malformed error form, the left-over error form, or a spelled text, which never opens with 'E' (rn.str_not_err).

def rn.errs(d: Wr.Dec<FRn.Req>, e: {LawsBase.wire_opens_err(FRn.ffi.got(d)) == True{} : Bool}) -> {Bool.or(LawsBase.text_same(FRn.ffi.got(d), Wr.err("retry_note: malformed request")), LawsBase.text_same(FRn.ffi.got(d), Wr.err("retry_note: input left after the request"))) == True{} : Bool}:
  match d:
    case Wr.Got{q, r}:
      match q:
        case FRn.Req{+a, +c}:
          match r:
            case SNil{}:
              LARetryNote.rn.absurd({Bool.or(LawsBase.text_same(Wr.put_str(Rn.text(a, c), ""), Wr.err("retry_note: malformed request")), LawsBase.text_same(Wr.put_str(Rn.text(a, c), ""), Wr.err("retry_note: input left after the request"))) == True{} : Bool}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Wr.put_str(Rn.text(a, c), "")), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_str(Rn.text(a, c), "")), False{}, LARetryNote.rn.str_not_err(Rn.text(a, c), "")), e))
            case SCon{h, t}:
              {==}
    case Wr.Bad{}:
      {==}

def RetryNote.retry_note_ffi_errors(s, e):
  rn.errs(FRn.get_req(Wr.get_nat(s)), e)
