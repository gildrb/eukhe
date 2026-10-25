# eukhe: the proof of LAW dash_policy_spec
#
# PROOF: the code tests a name against each table as the spec does
# (dpb.listed, on the code's tables, which are the spec's), and both pick
# the verdict from the two tests the same way (dps.pick: case by case).

import Base
import ../../bend/dash_policy.bend as Dp
import ../../laws/dash_policy.bend as DashPolicy
import ./base.bend as LA

def dps.pick(c: Bool, s: Bool) -> {Dp.verdict.of(c, s) == DashPolicy.dp_verdict.pick(c, s) : Dp.Verdict}:
  match c s:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def DashPolicy.dash_policy_spec(n):
  %LA.dpb.listed(n, Dp.catalog()) : {Dp.verdict(n) == DashPolicy.dp_verdict.pick(_, DashPolicy.dp_in(n, DashPolicy.dp_session())) : Dp.Verdict}
  %LA.dpb.listed(n, Dp.session()) : {Dp.verdict(n) == DashPolicy.dp_verdict.pick(Dp.listed(n, Dp.catalog()), _) : Dp.Verdict}
  dps.pick(Dp.listed(n, Dp.catalog()), Dp.listed(n, Dp.session()))
