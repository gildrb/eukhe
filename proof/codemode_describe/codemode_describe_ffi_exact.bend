# eukhe: the proof of LAW codemode_describe_ffi_exact

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../bend/ffi_codemode_describe.bend as FDsc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_describe.bend as CodemodeDescribe
import ../context_order/base.bend as LACo
import ./base/exact.bend as LACdExact

# PROOF of LAW codemode_describe_ffi_exact: the request decoder answers Got only for a spelled request whose numbers fit (cde.req); the entry answers a value only when nothing is left after it.

def cdx.top(-s: String, d: Wr.Dec<FDsc.Req>, p: LACdExact.cde.RQ(s, d), ok: {LawsBase.wire_opens_err(FDsc.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FDsc.Req, q2 => {s == CodemodeDescribe.spell_req(q2, "") : String} & {CodemodeDescribe.req_fits(q2) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, p)
        case SCon{x, y}:
          LACo.co.tf(Sigma<&1, &1, FDsc.Req, q2 => {s == CodemodeDescribe.spell_req(q2, "") : String} & {CodemodeDescribe.req_fits(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LACo.co.tf(Sigma<&1, &1, FDsc.Req, q2 => {s == CodemodeDescribe.spell_req(q2, "") : String} & {CodemodeDescribe.req_fits(q2) == True{} : Bool}>, ok)

def CodemodeDescribe.codemode_describe_ffi_exact(s, ok):
  cdx.top(s, FDsc.get_req(s), LACdExact.cde.req(s), ok)
