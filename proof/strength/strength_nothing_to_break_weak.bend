# eukhe: the proof of LAW strength_nothing_to_break_weak
#
# PROOF: the mark is on the state now (LS.sv.eq_refl); 0 planned is at most 0
# ran, and 0 ran is no break, so the model answers weak.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_nothing_to_break_weak(pct, c, now):
  %LS.sv.eq_refl(now) : {St.strength.on(_, 1n+pct, c, 0n, 0n) == St.Weak{} : St.Strength}
  {==}
