# eukhe: the proof of LAW strength_label_done_needs_certified
#
# PROOF: the spec's certified is the model's (LS.sg.certified); a label that
# says done comes from a passing label with the model's certified true
# (LS.sg.done: a failed or unverified label never says done).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_label_done_needs_certified(l, now, gs, done):
  %LS.sg.certified(now, gs) : {_ == True{} : Bool}
  LS.sg.done(l, now, gs, done)
