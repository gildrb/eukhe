# eukhe: the proof of LAW strength_settle_is_spec
#
# PROOF: by cases on verify's label; a passing claim's first due check is the
# spec's lead when the spec counts one due (LS.sg.due: induction on the
# checks), else the label, the spec's (LS.sg.settle).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_settle_is_spec(l, now, gs):
  LS.sg.settle(l, now, gs)
