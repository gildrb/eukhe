# eukhe: the proof of LAW strength_settle_ends_done_certified
#
# PROOF: the spec's certified is the model's (LS.sg.certified); a step that ends
# done is the end of a passing claim with no check due, whose label says
# done (LS.sg.ends), so certified holds (LS.sg.done).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_settle_ends_done_certified(l, now, gs, done):
  %LS.sg.certified(now, gs) : {_ == True{} : Bool}
  LS.sg.ends(l, now, gs, done)
