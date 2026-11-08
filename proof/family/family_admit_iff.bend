# eukhe: the proof of LAW family_admit_iff
#
# PROOF: the decision is the three-step verdict (fp.decide_eq), which admits exactly when the spec admits (fa.verdict).

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF


def Family.family_admit_iff(d, m, r, c, ws):
  %Equal.sym(F.Verdict, F.decide(d, m, r, c, ws), LF.fp.verdict(d, m, r, c, ws), LF.fp.decide_eq(d, m, r, c, ws)) : {Family.fam_admitted(_) == FamSpec.admits(d, m, r, c, ws) : Bool}
  LF.fa.verdict(d, m, r, c, ws)
