# eukhe: the proof of LAW family_admit_iff
#
# PROOF: the decision is the spec's verdict (family_refusal_precedence), which admits exactly when the spec admits (fa.verdict).

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF
import ./family_refusal_precedence.bend as PFamilyRefusalPrecedence


def Family.family_admit_iff(d, m, r, c, ws):
  %Equal.sym(F.Verdict, F.decide(d, m, r, c, ws), FamSpec.verdict(d, m, r, c, ws), Family.family_refusal_precedence(d, m, r, c, ws)) : {Family.fam_admitted(_) == FamSpec.admits(d, m, r, c, ws) : Bool}
  LF.fa.verdict(d, m, r, c, ws)
