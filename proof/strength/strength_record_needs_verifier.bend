# eukhe: the proof of LAW strength_record_needs_verifier
#
# PROOF: by cases on who acts: the owner and the worker are refused with the
# checks kept; the verifier contradicts the premise.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../laws/strength.bend as Strength
import ./base/model.bend as LS

def Strength.strength_record_needs_verifier(who, i, m, gs, no):
  match who:
    case V.Owner{}:
      {==}
    case V.Worker{}:
      {==}
    case V.Verifier{}:
      LS.sg.absurd_t({St.record(V.Verifier{}, i, m, gs) == (False{}, gs) : Bool & List<&2, St.Gauge>}, no)
