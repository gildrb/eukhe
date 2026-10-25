# eukhe: the proof of LAW dash_policy_entry_refuses
#
# PROOF: the entry answers either a verdict, which opens with a Nat (never
# 'E': wire_nat_not_err), or the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/dash_policy.bend as Dp
import ../../bend/ffi_dash_policy.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/dash_policy.bend as DashPolicy
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def dpf.refuse(d: Wr.Dec<String>, bad: {LawsBase.wire_opens_err(FDp.ffi.got(d)) == True{} : Bool}) -> {FDp.ffi.got(d) == Wr.err("dash_policy: malformed request") : String}:
  match d:
    case Wr.Got{+n, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FDp.answer(n) == Wr.err("dash_policy: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FDp.answer(n)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FDp.answer(n)), True{}, bad), Wire.wire_nat_not_err(FDp.tag(Dp.verdict(n)), "")))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def DashPolicy.dash_policy_entry_refuses(s, bad):
  dpf.refuse(FDp.get_req(s), bad)
