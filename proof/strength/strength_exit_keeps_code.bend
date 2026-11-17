# eukhe: the proof of LAW strength_exit_keeps_code
#
# PROOF: by cases on whether every check holds and on certified: a nonzero code
# stays in each (LS.sg.keep).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_exit_keeps_code(p, now, slots, gs):
  LS.sg.keep(V.holds(now, slots), p, now, slots, gs)
