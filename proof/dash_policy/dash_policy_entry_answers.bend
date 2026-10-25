# eukhe: the proof of LAW dash_policy_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (dash_policy_entry_reads), so the entry answers the code's verdict,
# which is the spec's (dash_policy_spec), with the spec's tag (dpa.tag:
# case by case).

import Base
import ../../bend/dash_policy.bend as Dp
import ../../bend/ffi_dash_policy.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/dash_policy.bend as DashPolicy
import ./dash_policy_spec.bend as PDashPolicySpec
import ./dash_policy_entry_reads.bend as PDashPolicyEntryReads

def dpa.tag(v: Dp.Verdict) -> {FDp.tag(v) == DashPolicy.dp_tag(v) : Nat}:
  match v:
    case Dp.ForSession{}:
      {==}
    case Dp.ForCatalog{}:
      {==}
    case Dp.NotRun{}:
      {==}

def DashPolicy.dash_policy_entry_answers(n, h):
  %Equal.sym(Wr.Dec<String>, FDp.get_req(Wr.put_str(n, "")), Wr.Got{n, ""}, DashPolicy.dash_policy_entry_reads(n, "", h)) : {FDp.ffi.got(_) == DashPolicy.dp_reply(n) : String}
  %Equal.sym(Dp.Verdict, Dp.verdict(n), DashPolicy.dp_verdict(n), DashPolicy.dash_policy_spec(n)) : {Wr.put_nat(FDp.tag(_), "") == DashPolicy.dp_reply(n) : String}
  %dpa.tag(DashPolicy.dp_verdict(n)) : {Wr.put_nat(FDp.tag(DashPolicy.dp_verdict(n)), "") == Wr.put_nat(_, "") : String}
  {==}
