# eukhe: the proof of LAW headless_task_exit_stands
#
# PROOF: case analysis on the cause, the goal and the reading: every case with no work left and a verdict computes to the exit of its cause, standing; the others contradict a premise.

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

def HeadlessTask.headless_task_exit_stands(f, h, u):
  match f:
    case Ht.Facts{c, g, r}:
      match c:
        case Hx.CAnswered{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, u))
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, u))
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
                case Ht.RDone{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
                case Ht.RLeft{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
                case Ht.RUnjudged{}:
                  LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
        case Hx.CCommandFailed{}:
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Complete{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
            case Ht.Open{}:
              match r:
                case Ht.RUnasked{}:
                  {==}
                case Ht.RDone{}:
                  {==}
                case Ht.RLeft{}:
                  {==}
                case Ht.RUnjudged{}:
                  {==}
