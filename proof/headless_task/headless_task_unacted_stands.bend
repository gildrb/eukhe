# eukhe: the proof of LAW headless_task_unacted_stands
#
# PROOF: case analysis: a run that did not act computes to the exit of its cause, standing; the other cases contradict a premise.

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

def HeadlessTask.headless_task_unacted_stands(f, u):
  match f:
    case Ht.Facts{c, a, r}:
      match c:
        case Hx.CAnswered{}:
          match a:
            case True{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
