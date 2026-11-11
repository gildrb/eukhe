# eukhe: the proof of LAW quirks_faults_iff_rejected
# No verdict is a fault exactly when every verdict is fine (QV.qv.faults);
# the model's verdicts are all fine exactly when the spec's scan is
# (QP.qp.fine_all), which is exactly when the rulebook compiles
# (QP.qp.all_fine).

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP
import ./base/verdicts.bend as QV

def Quirks.quirks_faults_iff_rejected(known, rs):
  Equal.trans(Bool, Nat.is_eq(Quirks.qs_faults(If.verdicts(known, rs)), 0n), If.fine_all(If.verdicts.go(rs, known, 0n)), If.compiles(known, rs),
    QV.qv.faults(If.verdicts(known, rs)),
    Equal.trans(Bool, If.fine_all(If.verdicts.go(rs, known, 0n)), QP.qp.all_fine_spec(rs, known), If.compiles(known, rs), QP.qp.fine_all(rs, known, 0n), QP.qp.all_fine(rs, known)))
