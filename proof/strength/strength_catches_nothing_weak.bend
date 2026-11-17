# eukhe: the proof of LAW strength_catches_nothing_weak
#
# PROOF: the mark is on the state now (LS.sv.eq_refl) and whole (LS.sg.le_refl);
# one or more breaks ran and none was caught, so the catch is short of
# any share above 0 (LS.sg.weak).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_catches_nothing_weak(pct, now, k):
  LS.sg.weak(1n+pct, 0n, 1n+k, 1n+k, now, LS.sg.le_refl(1n+k), {==}, {==})
