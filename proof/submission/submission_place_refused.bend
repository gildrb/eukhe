# eukhe: the proof of LAW submission_place_refused

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

# PROOF of LAW submission_place_refused: case on the submission: a settled or queued one contradicts a premise; a placed input refuses by computation.

def Submission.submission_place_refused(s, e, open, nq):
  match s:
    case Sb.InQueued{}:
      LLogicLogic.pt.absurd({Sb.step(Sb.InQueued{}, Sb.Place{e}) == Sb.Refused{Sb.NotQueued{}} : Sb.Out}, nq)
    case Sb.InPlaced{f}:
      {==}
    case Sb.InAnswered{f, a}:
      LLogicLogic.pt.absurd({Sb.step(Sb.InAnswered{f, a}, Sb.Place{e}) == Sb.Refused{Sb.NotQueued{}} : Sb.Out}, open)
    case Sb.InDropped{m}:
      LLogicLogic.pt.absurd({Sb.step(Sb.InDropped{m}, Sb.Place{e}) == Sb.Refused{Sb.NotQueued{}} : Sb.Out}, open)
    case Sb.WrQueued{}:
      LLogicLogic.pt.absurd({Sb.step(Sb.WrQueued{}, Sb.Place{e}) == Sb.Refused{Sb.NotQueued{}} : Sb.Out}, nq)
    case Sb.WrPlaced{f}:
      LLogicLogic.pt.absurd({Sb.step(Sb.WrPlaced{f}, Sb.Place{e}) == Sb.Refused{Sb.NotQueued{}} : Sb.Out}, open)
    case Sb.WrDropped{}:
      LLogicLogic.pt.absurd({Sb.step(Sb.WrDropped{}, Sb.Place{e}) == Sb.Refused{Sb.NotQueued{}} : Sb.Out}, open)
