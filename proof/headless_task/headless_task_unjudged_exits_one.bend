# eukhe: the proof of LAW headless_task_unjudged_exits_one
#
# PROOF: case analysis on the cause, the goal and the reading: an answer without an open goal and without a verdict computes to exit 1 unjudged; every other case contradicts the premise.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../spec/durable/headless_task.bend as SpT
import ../../laws/headless_task.bend as HeadlessTask
import ../base/logic/logic.bend as LLogicLogic

def HeadlessTask.headless_task_unjudged_exits_one(f, h):
  match f:
    case Ht.Facts{c, g, r}:
      match c:
        case Hx.CAnswered{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CCommandFailed{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CGaveUp{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CRunFailed{x}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CProviderError{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CAborted{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CUnfinished{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CSlashFailed{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CCompactionFailed{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CAutonomousFailed{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CBudgetLimited{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CBudgetUnanswered{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{1n, Ht.Unjudged{}} : Ht.Verdict}, h)
