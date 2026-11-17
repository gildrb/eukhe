# eukhe: the proof of LAW strength_exit_is_spec
#
# PROOF: verify's every-check-holds fold is the spec's count (LS.sv.holds); then
# by cases on it, with the model's certified the spec's (LS.sg.exit).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_exit_is_spec(base, now, slots, gs):
  LS.sg.exit(base, now, slots, gs)
