# eukhe: the proof of LAW strength_certified_needs_strong
#
# PROOF: the model's shown fold is the spec's count of strong checks
# (LS.sg.shown); that count is 0, so shown is false.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_certified_needs_strong(now, gs, none):
  %Equal.sym(Bool, St.shown(now, gs), Bool.not(Nat.is_eq(S.strongs(now, gs), 0n)), LS.sg.shown(now, gs)) : {Bool.and(_, St.clear(now, gs)) == False{} : Bool}
  %Equal.sym(Nat, S.strongs(now, gs), 0n, none) : {Bool.and(Bool.not(Nat.is_eq(_, 0n)), St.clear(now, gs)) == False{} : Bool}
  {==}
