# eukhe: the proof of LAW retry_ffi_entry_left_over_exact
# The left-over error comes only from a request the decoder read with
# input after it: a malformed input answers another text, and a request
# read whole a decision, never an error form (LARetryFfi.rf.answer_err).
# What the decoder reads is the encoding of that request and of the input
# after it (retry_ffi_request_exact), which the laws spell
# (LARetryFfi.rf.req), and fits the wire (LARetryFfi.rf.fr).

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/retry.bend as Retry
import ../../laws/retry_ffi.bend as RetryFfi
import ../retry/retry_ffi_request_exact.bend as PRetryFfiRequestExact
import ../base/staging.bend as LStg
import ./base.bend as LARetryFfi

def rflx.Out(s: String) -> Type:
  Sigma<&1, &1, Fr.Req, q => Sigma<&1, &1, Char, h => Sigma<&1, &1, String, t => {s == RetryFfi.spell_req(q, SCon{h, t}) : String} & {Retry.rs.req_fits(q) == True{} : Bool}>>>

def rflx.top(+s: String, d: Wr.Dec<Fr.Req>, ed: {Fr.get_req(s) == d : Wr.Dec<Fr.Req>}, fr: LARetryFfi.rf.FR(d), e: {Fr.ffi.got(d) == Wr.err("retry: input left after the request") : String}) -> rflx.Out(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LARetryFfi.rf.answer_err(rflx.Out(s), q, "retry: input left after the request", e)
        case SCon{+h, +t}:
          (q, (h, (t, (Equal.trans(String, s, Fr.put_req(q, SCon{h, t}), RetryFfi.spell_req(q, SCon{h, t}), Retry.retry_ffi_request_exact(s, q, SCon{h, t}, ed), Equal.sym(String, RetryFfi.spell_req(q, SCon{h, t}), Fr.put_req(q, SCon{h, t}), LARetryFfi.rf.req(q, SCon{h, t}))), fr))))
    case Wr.Bad{}:
      LStg.stg.absurdF(rflx.Out(s), Equal.cong(String, Bool, z => LawsBase.text_same(z, Wr.err("retry: input left after the request")), Wr.err("retry: malformed request"), Wr.err("retry: input left after the request"), e))

def RetryFfi.retry_ffi_entry_left_over_exact(s, e):
  rflx.top(s, Fr.get_req(s), {==}, LARetryFfi.rf.fr(s), e)
