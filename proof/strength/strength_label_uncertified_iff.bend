# eukhe: the proof of LAW strength_label_uncertified_iff
#
# PROOF: by cases on verify's label; a passing one is not certified exactly when
# the model's certified, the spec's (LS.sg.certified), is false (LS.sg.uc).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_label_uncertified_iff(l, now, gs):
  match l:
    case V.Verified{}:
      %LS.sg.certified(now, gs) : {S.is_uncertified(St.label.cert(St.certified(now, gs), V.Verified{})) == Bool.not(_) : Bool}
      LS.sg.uc(St.certified(now, gs), V.Verified{}, {==})
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      %LS.sg.certified(now, gs) : {S.is_uncertified(St.label.cert(St.certified(now, gs), V.Passed{})) == Bool.not(_) : Bool}
      LS.sg.uc(St.certified(now, gs), V.Passed{}, {==})
