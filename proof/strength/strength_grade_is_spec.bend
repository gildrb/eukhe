# eukhe: the proof of LAW strength_grade_is_spec
#
# PROOF: the model's grade of a check is the spec's, case by case on the bar and
# the mark; a measured mark through each stage of the model (LS.sg.strength).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_grade_is_spec(now, g):
  LS.sg.strength(now, g)
