# eukhe: the proof of LAW strength_ungauged_free
#
# PROOF: by the model's definition: an exempt or waived bar is free before the
# mark is read, and so is a share of 0 (strength.needs).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_ungauged_free(now, m):
  ({==}, ({==}, {==}))
