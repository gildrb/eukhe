# eukhe: the proof of LAW verify_label_is_spec
#
# PROOF: the model's folds are the spec's counts (LL.vl.refuted, LL.vl.holds);
# then the cases of the count of the refuted, of the checks and of
# confinement (LL.vl.label.of).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_label_is_spec(conf, now, slots):
  %LL.vl.refuted(now, slots) : {V.label.of(conf, _, Bool.and(V.some(slots), V.holds(now, slots))) == S.label(conf, now, slots) : V.Label}
  %LL.vl.holds(now, slots) : {V.label.of(conf, Bool.not(Nat.is_eq(S.refuted(now, slots), 0n)), Bool.and(V.some(slots), _)) == S.label(conf, now, slots) : V.Label}
  LL.vl.label.of(conf, S.refuted(now, slots), slots, S.confirmed(now, slots))
