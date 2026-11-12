# eukhe: the proof of LAW retry_ffi_entry_exact
# The entry answers a value only for a request it read whole, with nothing
# left; what its decoder reads is the encoding of that request
# (retry_ffi_request_exact), which the laws spell (LARetryFfi.rf.req), and
# fits the wire (LARetryFfi.rf.fr).

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/retry.bend as Retry
import ../../laws/retry_ffi.bend as RetryFfi
import ../retry/retry_ffi_request_exact.bend as PRetryFfiRequestExact
import ../base/staging.bend as LStg
import ./base.bend as LARetryFfi

def rfx.top(+s: String, d: Wr.Dec<Fr.Req>, ed: {Fr.get_req(s) == d : Wr.Dec<Fr.Req>}, fr: LARetryFfi.rf.FR(d), ok: {LawsBase.wire_opens_err(Fr.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, Fr.Req, q => {s == RetryFfi.spell_req(q, "") : String} & {Retry.rs.req_fits(q) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, (Equal.trans(String, s, Fr.put_req(q, ""), RetryFfi.spell_req(q, ""), Retry.retry_ffi_request_exact(s, q, "", ed), Equal.sym(String, RetryFfi.spell_req(q, ""), Fr.put_req(q, ""), LARetryFfi.rf.req(q, ""))), fr))
        case SCon{h, t}:
          LStg.stg.absurd(Sigma<&1, &1, Fr.Req, q2 => {s == RetryFfi.spell_req(q2, "") : String} & {Retry.rs.req_fits(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Fr.Req, q2 => {s == RetryFfi.spell_req(q2, "") : String} & {Retry.rs.req_fits(q2) == True{} : Bool}>, ok)

def RetryFfi.retry_ffi_entry_exact(s, ok):
  rfx.top(s, Fr.get_req(s), {==}, LARetryFfi.rf.fr(s), ok)
