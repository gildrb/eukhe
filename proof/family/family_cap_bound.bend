# eukhe: the proof of LAW family_cap_bound
#
# PROOF: an admitted decision admits (cong of e), so the spec admits (family_admit_iff), so its cap part holds.

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF
import ./family_admit_iff.bend as PFamilyAdmitIff
import ../base/logic/bool.bend as LLogicBool


def Family.family_cap_bound(d, m, r, c, ws, k, e):
  +h = Equal.trans(Bool, FamSpec.admits(d, m, r, c, ws), Family.fam_admitted(F.decide(d, m, r, c, ws)), True{}, Equal.sym(Bool, Family.fam_admitted(F.decide(d, m, r, c, ws)), FamSpec.admits(d, m, r, c, ws), Family.family_admit_iff(d, m, r, c, ws)), Equal.cong(F.Verdict, Bool, v => Family.fam_admitted(v), F.decide(d, m, r, c, ws), F.Admit{k}, e))
  +h2 = LLogicBool.tree.pt.and_r(FamSpec.all_ok(ws), Bool.and(Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, List.length(&2, String, ws))), h)
  LLogicBool.tree.pt.and_r(Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, List.length(&2, String, ws)), h2)
