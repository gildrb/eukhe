# eukhe: the proof of LAW verify_unconfined_qualifier_exact
#
# PROOF: the label is the model's label of whether a check is refuted and
# whether every check holds; the cases of confinement and of those two
# (LL.vl.qualifier).

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL

def Verify.verify_unconfined_qualifier_exact(conf, now, slots):
  LL.vl.qualifier(conf, V.refuted(now, slots), Bool.and(V.some(slots), V.holds(now, slots)))
