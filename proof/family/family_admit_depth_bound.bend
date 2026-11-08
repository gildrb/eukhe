# eukhe: the proof of LAW family_admit_depth_bound
#
# PROOF: the decision is the three-step verdict (fp.decide_eq); an admitted verdict passed no bad why, the depth below the bound and the cap, and names the depth plus one (fd.of).

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF


def Family.family_admit_depth_bound(d, m, r, c, ws, k, e):
  LF.fd.of(FamSpec.first_bad(ws, 0n), d, m, r, c, List.length(&2, String, ws), k, Equal.trans(F.Verdict, LF.fp.verdict(d, m, r, c, ws), F.decide(d, m, r, c, ws), F.Admit{k}, Equal.sym(F.Verdict, F.decide(d, m, r, c, ws), LF.fp.verdict(d, m, r, c, ws), LF.fp.decide_eq(d, m, r, c, ws)), e))
