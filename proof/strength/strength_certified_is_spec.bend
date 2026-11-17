# eukhe: the proof of LAW strength_certified_is_spec
#
# PROOF: the model's folds are the spec's counts (LS.sg.shown, LS.sg.clear),
# each check graded as the spec grades it (LS.sg.strength).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_certified_is_spec(now, gs):
  LS.sg.certified(now, gs)
