# eukhe: the proof of LAW retry_note_ffi_exact

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

# PROOF of LAW retry_note_ffi_exact: what the decoder reads is spelled, and so is the input after it (rn.pr), and it fits the wire (rn.fr); a reply that is no error form has nothing after the request, so the input is the spelled request.

def rn.ex(-s: String, d: Wr.Dec<FRn.Req>, pr: LARetryNote.rn.PR(s, d), fr: LARetryNote.rn.FR(d), ok: {LawsBase.wire_opens_err(FRn.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FRn.Req, q => {s == RetryNote.spell_req(q, "") : String} & {RetryNote.req_fits(q) == True{} : Bool}>:
  match d:
    case Wr.Got{q, r}:
      match q:
        case FRn.Req{+a, +c}:
          match r:
            case SNil{}:
              (FRn.Req{a, c}, (pr, fr))
            case SCon{h, t}:
              LARetryNote.rn.absurd_t(Sigma<&1, &1, FRn.Req, q => {s == RetryNote.spell_req(q, "") : String} & {RetryNote.req_fits(q) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LARetryNote.rn.absurd_t(Sigma<&1, &1, FRn.Req, q => {s == RetryNote.spell_req(q, "") : String} & {RetryNote.req_fits(q) == True{} : Bool}>, ok)

def RetryNote.retry_note_ffi_exact(s, ok):
  rn.ex(s, FRn.get_req(Wr.get_nat(s)), LARetryNote.rn.pr(s), LARetryNote.rn.fr(s), ok)
