# eukhe: the proof of LAW submission_answer_refused

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

# PROOF of LAW submission_answer_refused: case on the submission: a settled one or a placed input contradicts a premise; a queued input or write refuses by computation.

def Submission.submission_answer_refused(s, a, open, np):
  match s:
    case Sb.InQueued{}:
      {==}
    case Sb.InPlaced{f}:
      LLogicLogic.pt.absurd({Sb.step(Sb.InPlaced{f}, Sb.Answer{a}) == Sb.Refused{Sb.NotPlacedInput{}} : Sb.Out}, np)
    case Sb.InAnswered{f, b}:
      LLogicLogic.pt.absurd({Sb.step(Sb.InAnswered{f, b}, Sb.Answer{a}) == Sb.Refused{Sb.NotPlacedInput{}} : Sb.Out}, open)
    case Sb.InDropped{m}:
      LLogicLogic.pt.absurd({Sb.step(Sb.InDropped{m}, Sb.Answer{a}) == Sb.Refused{Sb.NotPlacedInput{}} : Sb.Out}, open)
    case Sb.WrQueued{}:
      {==}
    case Sb.WrPlaced{f}:
      LLogicLogic.pt.absurd({Sb.step(Sb.WrPlaced{f}, Sb.Answer{a}) == Sb.Refused{Sb.NotPlacedInput{}} : Sb.Out}, open)
    case Sb.WrDropped{}:
      LLogicLogic.pt.absurd({Sb.step(Sb.WrDropped{}, Sb.Answer{a}) == Sb.Refused{Sb.NotPlacedInput{}} : Sb.Out}, open)
