# eukhe: the proof of LAW family_batch_all_or_none
#
# PROOF: each decision admits exactly when the spec admits (family_admit_iff); the spec's admission of xs ++ ys splits: its reasons (fb.all), its size (fb.len) and the cap (fb.cap), joined by a Bool identity (fb.bool5).

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF
import ./family_admit_iff.bend as PFamilyAdmitIff

def Family.family_batch_all_or_none(d, m, r, c, xs, ys):
  %Equal.sym(Bool, Family.fam_admitted(F.decide(d, m, r, c, List.append(&2, String, xs, ys))), FamSpec.admits(d, m, r, c, List.append(&2, String, xs, ys)), Family.family_admit_iff(d, m, r, c, List.append(&2, String, xs, ys))) : {_ == Bool.and(Family.fam_admitted(F.decide(d, m, r, c, xs)), Family.fam_admitted(F.decide(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys))) : Bool}
  %Equal.sym(Bool, Family.fam_admitted(F.decide(d, m, r, c, xs)), FamSpec.admits(d, m, r, c, xs), Family.family_admit_iff(d, m, r, c, xs)) : {FamSpec.admits(d, m, r, c, List.append(&2, String, xs, ys)) == Bool.and(_, Family.fam_admitted(F.decide(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys))) : Bool}
  %Equal.sym(Bool, Family.fam_admitted(F.decide(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys)), FamSpec.admits(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys), Family.family_admit_iff(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys)) : {FamSpec.admits(d, m, r, c, List.append(&2, String, xs, ys)) == Bool.and(FamSpec.admits(d, m, r, c, xs), _) : Bool}
  %Equal.sym(Bool, FamSpec.all_ok(List.append(&2, String, xs, ys)), Bool.and(FamSpec.all_ok(xs), FamSpec.all_ok(ys)), LF.fb.all(xs, ys)) : {Bool.and(_, Bool.and(Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, List.length(&2, String, List.append(&2, String, xs, ys))))) == Bool.and(FamSpec.admits(d, m, r, c, xs), FamSpec.admits(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys)) : Bool}
  %Equal.sym(Nat, List.length(&2, String, List.append(&2, String, xs, ys)), Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), LF.fb.len(xs, ys)) : {Bool.and(Bool.and(FamSpec.all_ok(xs), FamSpec.all_ok(ys)), Bool.and(Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, _))) == Bool.and(FamSpec.admits(d, m, r, c, xs), FamSpec.admits(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys)) : Bool}
  %Equal.sym(Bool, FamSpec.cap_ok(r, c, Nat.add(List.length(&2, String, xs), List.length(&2, String, ys))), Bool.and(FamSpec.cap_ok(r, c, List.length(&2, String, xs)), FamSpec.cap_ok(Nat.add(r, List.length(&2, String, xs)), c, List.length(&2, String, ys))), LF.fb.cap(r, c, List.length(&2, String, xs), List.length(&2, String, ys))) : {Bool.and(Bool.and(FamSpec.all_ok(xs), FamSpec.all_ok(ys)), Bool.and(Bool.not(FamSpec.deep(d, m)), _)) == Bool.and(FamSpec.admits(d, m, r, c, xs), FamSpec.admits(d, m, Nat.add(r, List.length(&2, String, xs)), c, ys)) : Bool}
  LF.fb.bool5(FamSpec.all_ok(xs), FamSpec.all_ok(ys), Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, List.length(&2, String, xs)), FamSpec.cap_ok(Nat.add(r, List.length(&2, String, xs)), c, List.length(&2, String, ys)))
