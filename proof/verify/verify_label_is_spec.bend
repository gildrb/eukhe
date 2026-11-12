# eukhe: the proof of LAW verify_label_is_spec
#
# PROOF: the model's folds are the spec's counts (LL.vl.refuted, LL.vl.holds);
# then the cases of the count of the refuted and of the checks
# (LL.vl.label.of).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_label_is_spec(now, slots):
  %LL.vl.refuted(now, slots) : {V.label.of(_, Bool.and(V.some(slots), V.holds(now, slots))) == S.label(now, slots) : V.Label}
  %LL.vl.holds(now, slots) : {V.label.of(Bool.not(Nat.is_eq(S.refuted(now, slots), 0n)), Bool.and(V.some(slots), _)) == S.label(now, slots) : V.Label}
  LL.vl.label.of(S.refuted(now, slots), slots, S.confirmed(now, slots))
