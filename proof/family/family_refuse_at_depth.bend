# eukhe: the proof of LAW family_refuse_at_depth
#
# PROOF: the decision is the three-step verdict (fp.decide_eq); with no bad why and the bound reached it is the depth refusal.

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF


def Family.family_refuse_at_depth(d, m, r, c, ws, ok, at):
  %Equal.sym(F.Verdict, F.decide(d, m, r, c, ws), LF.fp.verdict(d, m, r, c, ws), LF.fp.decide_eq(d, m, r, c, ws)) : {_ == F.Refuse{F.DepthLimit{}} : F.Verdict}
  %Equal.sym(Maybe<&2, Nat>, FamSpec.first_bad(ws, 0n), None{}, ok) : {LF.fp.verdict.of(_, d, m, r, c, List.length(&2, String, ws)) == F.Refuse{F.DepthLimit{}} : F.Verdict}
  %Equal.sym(Bool, Nat.is_le(m, d), True{}, at) : {LF.fp.verdict.deep(_, d, r, c, List.length(&2, String, ws)) == F.Refuse{F.DepthLimit{}} : F.Verdict}
  {==}
