# eukhe: the proof of LAW budget_share_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only for an input that is the
# spelling of q before rest, every number and count within the wire
# (bsx.req, stage by stage); the entry answers a start only for a request
# read whole with nothing left (bsx.top).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../bend/ffi_budget_share.bend as FBs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/budget_share.bend as BudgetShare
import ./base/entry.bend as BSE
import ../base/staging.bend as LStg

def bsx.top(-s: String, d: Wr.Dec<FBs.Req>, rp: BSE.bsx.RP(s, d), ok: {LawsBase.wire_opens_err(FBs.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FBs.Req, v => {s == BudgetShare.sh_w_req(v, "") : String} & {BudgetShare.sh_fit_req(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FBs.Req, v2 => {s == BudgetShare.sh_w_req(v2, "") : String} & {BudgetShare.sh_fit_req(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FBs.Req, v2 => {s == BudgetShare.sh_w_req(v2, "") : String} & {BudgetShare.sh_fit_req(v2) == True{} : Bool}>, ok)

def BudgetShare.budget_share_entry_exact(s, ok):
  bsx.top(s, FBs.get_req(s), BSE.bsx.req(s), ok)
