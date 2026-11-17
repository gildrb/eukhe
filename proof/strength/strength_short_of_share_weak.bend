# eukhe: the proof of LAW strength_short_of_share_weak
#
# PROOF: the mark is on the state now (LS.sv.eq_refl); the premises decide each
# later stage of the model (LS.sg.weak).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_short_of_share_weak(pct, c, n, p, now, whole, ran, short):
  LS.sg.weak(pct, c, n, p, now, whole, ran, short)
