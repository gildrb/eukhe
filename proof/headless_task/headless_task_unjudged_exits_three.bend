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
    case Ht.Facts{c, a, r}:
      match c:
        case Hx.CAnswered{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CCommandFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CGaveUp{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CRunFailed{x}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CProviderError{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CAborted{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CUnfinished{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CSlashFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CCompactionFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CAutonomousFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CBudgetLimited{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
        case Hx.CBudgetUnanswered{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, False{}, Ht.RDone{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, False{}, Ht.RLeft{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{3n, Ht.Unjudged{}} : Ht.Verdict}, h)
