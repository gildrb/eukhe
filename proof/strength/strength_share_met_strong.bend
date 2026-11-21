# eukhe: the proof of LAW strength_share_met_strong
#
# PROOF: the mark is on the state now (LS.sv.eq_refl); the premises decide each
# later stage of the model (LS.sg.strong).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_share_met_strong(pct, c, n, p, now, whole, ran, met):
  LS.sg.strong(pct, c, n, p, now, whole, ran, met)
