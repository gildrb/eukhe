# eukhe: the proof of LAW strength_label_is_spec
#
# PROOF: by cases on verify's label; a passing one through certified, which is
# the spec's (LS.sg.label).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_label_is_spec(l, now, gs):
  LS.sg.label(l, now, gs)
