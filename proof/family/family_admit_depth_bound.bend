# eukhe: the proof of LAW family_admit_depth_bound
#
# PROOF: the decision is the spec's verdict (family_refusal_precedence); an admitted spec verdict passed no bad why, the depth below the bound and the cap, and names the depth plus one (fd.of).

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF
import ./family_refusal_precedence.bend as PFamilyRefusalPrecedence


def Family.family_admit_depth_bound(d, m, r, c, ws, k, e):
  LF.fd.of(FamSpec.first_bad(ws, 0n), d, m, r, c, List.length(&2, String, ws), k, Equal.trans(F.Verdict, FamSpec.verdict(d, m, r, c, ws), F.decide(d, m, r, c, ws), F.Admit{k}, Equal.sym(F.Verdict, F.decide(d, m, r, c, ws), FamSpec.verdict(d, m, r, c, ws), Family.family_refusal_precedence(d, m, r, c, ws)), e))
