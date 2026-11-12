# eukhe: the proof of LAW submission_drop

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

# PROOF of LAW submission_drop: case on the submission: a settled one contradicts the premise; a queued input moves to the input unanswered with no entry, a placed input to the input unanswered at its entry, a queued write to the write unanswered, each by computation.

def Submission.submission_drop(s, open):
  match s:
    case Sb.InQueued{}:
      (Sb.InDropped{None{}}, ({==}, ({==}, ({==}, {==}))))
    case Sb.InPlaced{e}:
      (Sb.InDropped{Some{e}}, ({==}, ({==}, ({==}, {==}))))
    case Sb.InAnswered{e, a}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub, n => {Sb.step(Sb.InAnswered{e, a}, Sb.Drop{}) == Sb.Moves{n} : Sb.Out} & {Submission.unanswered_spec(n) == True{} : Bool} & {Submission.input_spec(n) == Submission.input_spec(Sb.InAnswered{e, a}) : Bool} & {Submission.entry_spec(n) == Submission.entry_spec(Sb.InAnswered{e, a}) : Maybe<&2, Nat>}>, open)
    case Sb.InDropped{m}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub, n => {Sb.step(Sb.InDropped{m}, Sb.Drop{}) == Sb.Moves{n} : Sb.Out} & {Submission.unanswered_spec(n) == True{} : Bool} & {Submission.input_spec(n) == Submission.input_spec(Sb.InDropped{m}) : Bool} & {Submission.entry_spec(n) == Submission.entry_spec(Sb.InDropped{m}) : Maybe<&2, Nat>}>, open)
    case Sb.WrQueued{}:
      (Sb.WrDropped{}, ({==}, ({==}, ({==}, {==}))))
    case Sb.WrPlaced{e}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub, n => {Sb.step(Sb.WrPlaced{e}, Sb.Drop{}) == Sb.Moves{n} : Sb.Out} & {Submission.unanswered_spec(n) == True{} : Bool} & {Submission.input_spec(n) == Submission.input_spec(Sb.WrPlaced{e}) : Bool} & {Submission.entry_spec(n) == Submission.entry_spec(Sb.WrPlaced{e}) : Maybe<&2, Nat>}>, open)
    case Sb.WrDropped{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub, n => {Sb.step(Sb.WrDropped{}, Sb.Drop{}) == Sb.Moves{n} : Sb.Out} & {Submission.unanswered_spec(n) == True{} : Bool} & {Submission.input_spec(n) == Submission.input_spec(Sb.WrDropped{}) : Bool} & {Submission.entry_spec(n) == Submission.entry_spec(Sb.WrDropped{}) : Maybe<&2, Nat>}>, open)
