# eukhe: the proof of LAW verify_failed_needs_refuted
#
# PROOF: some check is refuted exactly when the spec's count is not 0
# (LL.vl.refuted); the count is 0 by the premise, so the label is
# verified or unverified (LL.vl.unfailed).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_failed_needs_refuted(now, slots, none):
  %LL.vl.refuted(now, slots) : {Verify.sp_is_failed(V.label.of(_, Bool.and(V.some(slots), V.holds(now, slots)))) == False{} : Bool}
  %Equal.sym(Nat, S.refuted(now, slots), 0n, none) : {Verify.sp_is_failed(V.label.of(Bool.not(Nat.is_eq(_, 0n)), Bool.and(V.some(slots), V.holds(now, slots)))) == False{} : Bool}
  LL.vl.unfailed(Bool.and(V.some(slots), V.holds(now, slots)))
