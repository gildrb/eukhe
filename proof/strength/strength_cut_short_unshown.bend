# eukhe: the proof of LAW strength_cut_short_unshown
#
# PROOF: the mark is on the state now (LS.sv.eq_refl), but fewer breaks ran than
# were planned, so planned <= ran is false (LS.sg.lt_not_le) and the
# model answers unshown.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_cut_short_unshown(pct, c, n, p, now, short):
  %LS.sv.eq_refl(now) : {St.strength.on(_, pct, c, n, p) == St.Unshown{} : St.Strength}
  %LS.sg.lt_not_le(n, p, short) : {St.strength.full(_, pct, c, n) == St.Unshown{} : St.Strength}
  {==}
