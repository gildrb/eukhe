# eukhe: the proof of LAW retry_note_ffi_left_over_exact

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

# PROOF of LAW retry_note_ffi_left_over_exact: the left-over error comes only from a request the decoder read with input after it; what the decoder reads is spelled, and so is that input (rn.pr), and it fits the wire (rn.fr). A malformed request answers another text, and a whole request a spelled text, never an error form (rn.put_not_err).

def rn.lo(-s: String, d: Wr.Dec<FRn.Req>, pr: LARetryNote.rn.PR(s, d), fr: LARetryNote.rn.FR(d), e: {FRn.ffi.got(d) == Wr.err("retry_note: input left after the request") : String}) -> Sigma<&1, &1, RetryNote.LeftOver, w => {s == RetryNote.spell_left_over(w) : String} & {RetryNote.req_fits(RetryNote.left_req(w)) == True{} : Bool}>:
  match d:
    case Wr.Got{q, r}:
      match q:
        case FRn.Req{+a, +c}:
          match r:
            case SNil{}:
              LARetryNote.rn.put_not_err(Sigma<&1, &1, RetryNote.LeftOver, w => {s == RetryNote.spell_left_over(w) : String} & {RetryNote.req_fits(RetryNote.left_req(w)) == True{} : Bool}>, Rn.text(a, c), "retry_note: input left after the request", e)
            case SCon{+h, +t}:
              (RetryNote.LeftOver{FRn.Req{a, c}, h, t}, (pr, fr))
    case Wr.Bad{}:
      LARetryNote.rn.absurd(Sigma<&1, &1, RetryNote.LeftOver, w => {s == RetryNote.spell_left_over(w) : String} & {RetryNote.req_fits(RetryNote.left_req(w)) == True{} : Bool}>, Equal.cong(String, Bool, z => LawsBase.text_same(z, Wr.err("retry_note: input left after the request")), Wr.err("retry_note: malformed request"), Wr.err("retry_note: input left after the request"), e))

def RetryNote.retry_note_ffi_left_over_exact(s, e):
  rn.lo(s, FRn.get_req(Wr.get_nat(s)), LARetryNote.rn.pr(s), LARetryNote.rn.fr(s), e)
