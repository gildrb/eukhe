# eukhe: the proof of LAW submission_settled_stays

import Base
import ../../bend/submission.bend as Sb
import ../../bend/ffi_submission.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/wire.bend as LWire
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../../laws/submission.bend as Submission
import ./base.bend as LASubmission

# PROOF of LAW submission_settled_stays: case on the submission: an unsettled one contradicts the premise; a settled one stays by computation.

def Submission.submission_settled_stays(s, c, done):
  match s:
    case Sb.InQueued{}:
      LLogicLogic.absurd({Sb.queued_input(c) == Sb.Stays{} : Sb.Out}, done)
    case Sb.InPlaced{e}:
      LLogicLogic.absurd({Sb.placed_input(e, c) == Sb.Stays{} : Sb.Out}, done)
    case Sb.InAnswered{e, a}:
      {==}
    case Sb.InDropped{m}:
      {==}
    case Sb.WrQueued{}:
      LLogicLogic.absurd({Sb.queued_write(c) == Sb.Stays{} : Sb.Out}, done)
    case Sb.WrPlaced{e}:
      {==}
    case Sb.WrDropped{}:
      {==}
