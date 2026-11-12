# eukhe: the proof of LAW budget_share_entry_refuses
#
# PROOF: the entry answers either a start, a Nat (never 'E':
# wire_nat_not_err), or the one error form; so an answer that opens with
# 'E' is that error form.

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../bend/ffi_budget_share.bend as FBs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/budget_share.bend as BudgetShare
import ./base/entry.bend as BSE
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def bsf.refuse(d: Wr.Dec<FBs.Req>, bad: {LawsBase.wire_opens_err(FBs.ffi.got(d)) == True{} : Bool}) -> {FBs.ffi.got(d) == Wr.err("budget_share: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({Wr.put_nat(FBs.answer(q), "") == Wr.err("budget_share: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(Wr.put_nat(FBs.answer(q), "")), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_nat(FBs.answer(q), "")), True{}, bad), Wire.wire_nat_not_err(FBs.answer(q), "")))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def BudgetShare.budget_share_entry_refuses(s, bad):
  bsf.refuse(FBs.get_req(s), bad)
