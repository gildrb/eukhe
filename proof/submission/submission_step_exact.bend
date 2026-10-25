# eukhe: the proof of LAW submission_step_exact

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

# PROOF of LAW submission_step_exact: case on the submission and the change: each arm of the model computes to the spec's outcome.

def Submission.submission_step_exact(s, c):
  match s:
    case Sb.InQueued{}:
      match c:
        case Sb.Place{e}:
          {==}
        case Sb.Answer{a}:
          {==}
        case Sb.Drop{}:
          {==}
    case Sb.InPlaced{e}:
      match c:
        case Sb.Place{f}:
          {==}
        case Sb.Answer{a}:
          {==}
        case Sb.Drop{}:
          {==}
    case Sb.InAnswered{e, a}:
      {==}
    case Sb.InDropped{m}:
      {==}
    case Sb.WrQueued{}:
      match c:
        case Sb.Place{e}:
          {==}
        case Sb.Answer{a}:
          {==}
        case Sb.Drop{}:
          {==}
    case Sb.WrPlaced{e}:
      {==}
    case Sb.WrDropped{}:
      {==}
