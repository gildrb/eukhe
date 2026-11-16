# eukhe: the proof of LAW headless_task_unjudged_exits_three
#
# PROOF: case analysis: an answer the judge reads without a verdict computes to exit 3 unjudged; every other case contradicts the premise.

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

def HeadlessTask.headless_task_unjudged_exits_three(f, h):
  match f:
    case Ht.Facts{c, g, a, r}:
      match c:
        case Hx.CAnswered{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      {==}
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      {==}
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CCommandFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CGaveUp{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CRunFailed{x}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CProviderError{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CAborted{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CUnfinished{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CSlashFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CCompactionFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CAutonomousFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CBudgetLimited{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CBudgetUnanswered{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
