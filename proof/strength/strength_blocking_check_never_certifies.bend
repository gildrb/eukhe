# eukhe: the proof of LAW strength_blocking_check_never_certifies
#
# PROOF: the blocking check makes the model's clear fold false wherever it
# stands (LS.sg.clear_around: induction on the checks before it), so the
# conjunction is false (LS.sv.and_false).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_blocking_check_never_certifies(now, pre, g, post, weak):
  %LS.sg.clear_around(now, pre, g, post, weak) : {Bool.and(St.shown(now, Strength.sp_around(pre, g, post)), _) == False{} : Bool}
  Equal.sym(Bool, False{}, Bool.and(St.shown(now, Strength.sp_around(pre, g, post)), False{}), LS.sv.and_false(St.shown(now, Strength.sp_around(pre, g, post))))
