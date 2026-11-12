# eukhe: the proof of LAW budget_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only for an input that is the
# spelling of q before rest, every number and count within the wire
# (bx.req, field by field); the entry answers the model's decision only for
# a request read whole with nothing left (bex.top).

import Base
import ../../bend/budget.bend as B
import ../../bend/ffi_budget.bend as FBg
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/budget.bend as Budget
import ./base/exact.bend as BX
import ../base/staging.bend as LStg

def bex.top(-s: String, d: Wr.Dec<FBg.Req>, rp: BX.bx.RP(s, d), ok: {LawsBase.wire_opens_err(FBg.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FBg.Req, v => {s == Budget.sp_w_req(v, "") : String} & {Budget.sp_fit_req(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FBg.Req, v2 => {s == Budget.sp_w_req(v2, "") : String} & {Budget.sp_fit_req(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FBg.Req, v2 => {s == Budget.sp_w_req(v2, "") : String} & {Budget.sp_fit_req(v2) == True{} : Bool}>, ok)

def Budget.budget_entry_exact(s, ok):
  bex.top(s, FBg.get_req(s), BX.bx.req(s), ok)
