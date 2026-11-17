# eukhe: the proof of LAW strength_exit_uncertified_three
#
# PROOF: the model's exit is the spec's (LS.sg.exit); the premises decide every
# case of the spec's: all confirmed, some check, not certified, so a run of
# code 0 exits the unjudged code, which is 3.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_exit_uncertified_three(now, slots, gs, all, some, un):
  (LS.sg.three(now, slots, gs, all, some, un), {==})
