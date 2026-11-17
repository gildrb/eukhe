# eukhe: the proof of LAW strength_settle_unpassed_runs_nothing
#
# PROOF: by cases on verify's label: a passing one contradicts the premise; the
# others end at once with their label.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_settle_unpassed_runs_nothing(l, now, gs, no):
  match l:
    case V.Verified{}:
      LS.sg.absurd_t({St.settle(V.Verified{}, now, gs) == St.End{S.label(V.Verified{}, now, gs)} : St.Step}, no)
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      LS.sg.absurd_t({St.settle(V.Passed{}, now, gs) == St.End{S.label(V.Passed{}, now, gs)} : St.Step}, no)
