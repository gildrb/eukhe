# eukhe: the proof of LAW retry_ffi_entry_errors
# The entry answers a decision, which is no error form
# (LARetryFfi.rf.answer_ok), or one of its two error forms.

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/retry_ffi.bend as RetryFfi
import ../base/staging.bend as LStg
import ./base.bend as LARetryFfi

def rfe.top(d: Wr.Dec<Fr.Req>, bad: {LawsBase.wire_opens_err(Fr.ffi.got(d)) == True{} : Bool}) -> {Bool.or(LawsBase.text_same(Fr.ffi.got(d), Wr.err("retry: malformed request")), LawsBase.text_same(Fr.ffi.got(d), Wr.err("retry: input left after the request"))) == True{} : Bool}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({Bool.or(LawsBase.text_same(Fr.answer(q), Wr.err("retry: malformed request")), LawsBase.text_same(Fr.answer(q), Wr.err("retry: input left after the request"))) == True{} : Bool}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(Fr.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(Fr.answer(q)), True{}, bad), LARetryFfi.rf.answer_ok(q)))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def RetryFfi.retry_ffi_entry_errors(s, e):
  rfe.top(Fr.get_req(s), e)
