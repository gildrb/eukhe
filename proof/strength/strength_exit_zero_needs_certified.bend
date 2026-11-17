# eukhe: the proof of LAW strength_exit_zero_needs_certified
#
# PROOF: the model's exit is the spec's (LS.sg.exit); then by cases on whether
# every check is confirmed, the run's code and certified (LS.sg.ez.all).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_exit_zero_needs_certified(base, now, slots, gs):
  %Equal.sym(Nat, St.exit(base, now, slots, gs), S.exit(base, now, slots, gs), LS.sg.exit(base, now, slots, gs)) : {Nat.is_eq(_, 0n) == Bool.and(Nat.is_eq(base, 0n), Bool.and(SV.all_confirmed(now, slots), Bool.or(Nat.is_eq(List.length(&2, V.Slot, slots), 0n), S.certified(now, gs)))) : Bool}
  LS.sg.ez.all(SV.all_confirmed(now, slots), base, now, slots, gs)
