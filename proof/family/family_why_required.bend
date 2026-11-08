# eukhe: the proof of LAW family_why_required
#
# PROOF: the decision is the spec's verdict (family_refusal_precedence); with a bad why its first index is the refusal.

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF
import ./family_refusal_precedence.bend as PFamilyRefusalPrecedence


def Family.family_why_required(d, m, r, c, ws, i, e):
  %Equal.sym(F.Verdict, F.decide(d, m, r, c, ws), FamSpec.verdict(d, m, r, c, ws), Family.family_refusal_precedence(d, m, r, c, ws)) : {_ == F.Refuse{F.NoReason{i}} : F.Verdict}
  %Equal.sym(Maybe<&2, Nat>, FamSpec.first_bad(ws, 0n), Some{i}, e) : {FamSpec.verdict.of(_, d, m, r, c, List.length(&2, String, ws)) == F.Refuse{F.NoReason{i}} : F.Verdict}
  {==}
