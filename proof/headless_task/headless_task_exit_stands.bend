# eukhe: the proof of LAW headless_task_exit_stands
#
# PROOF: case analysis: every case with no work left, a verdict and no pending reading computes to the exit of its cause, standing; the others contradict a premise.

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

def HeadlessTask.headless_task_exit_stands(f, h, u, k):
  match f:
    case Ht.Facts{c, a, r}:
      match c:
        case Hx.CAnswered{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, k))
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, u))
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CCommandFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CGaveUp{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CRunFailed{x}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CProviderError{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CAborted{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CUnfinished{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CSlashFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CCompactionFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CAutonomousFailed{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CBudgetLimited{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
        case Hx.CBudgetUnanswered{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case False{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
