# eukhe: the proof of LAW family_cap_refusal_names_cap
#
# PROOF: the decision is the three-step verdict (fp.decide_eq); with no bad why (ok), the caller below the bound (below) and the batch past the cap (full) it is the cap refusal, naming c.

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF


def Family.family_cap_refusal_names_cap(d, m, r, c, ws, ok, below, full):
  %Equal.sym(F.Verdict, F.decide(d, m, r, c, ws), LF.fp.verdict(d, m, r, c, ws), LF.fp.decide_eq(d, m, r, c, ws)) : {_ == F.Refuse{F.FamilyFull{c}} : F.Verdict}
  %Equal.sym(Maybe<&2, Nat>, FamSpec.first_bad(ws, 0n), None{}, ok) : {LF.fp.verdict.of(_, d, m, r, c, List.length(&2, String, ws)) == F.Refuse{F.FamilyFull{c}} : F.Verdict}
  %Equal.sym(Bool, Nat.is_le(m, d), False{}, below) : {LF.fp.verdict.deep(_, d, r, c, List.length(&2, String, ws)) == F.Refuse{F.FamilyFull{c}} : F.Verdict}
  %Equal.sym(Bool, FamSpec.cap_ok(r, c, List.length(&2, String, ws)), False{}, full) : {LF.fp.verdict.cap(_, c, d) == F.Refuse{F.FamilyFull{c}} : F.Verdict}
  {==}
