# eukhe: the proof of LAW headless_task_unacted_stands
#
# PROOF: case analysis: a run that did not act and has no open goal computes to the exit of its cause, standing; the other cases contradict a premise.

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

def HeadlessTask.headless_task_unacted_stands(f, u, o):
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
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CCommandFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CGaveUp{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CRunFailed{x}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CRunFailed{x}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CProviderError{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CProviderError{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CAborted{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAborted{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CUnfinished{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CSlashFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CCompactionFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CAutonomousFailed{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CBudgetLimited{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
        case Hx.CBudgetUnanswered{}:
          match g:
            case Ht.NoGoal{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Complete{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
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
            case Ht.Open{}:
              match a:
                case True{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, u)
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, True{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, u)
                case False{}:
                  match r:
                    case Ht.RUnasked{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RUnasked{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RUnasked{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RDone{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RDone{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RDone{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RLeft{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RLeft{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RLeft{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
                    case Ht.RUnjudged{}:
                      LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RUnjudged{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}, False{}, Ht.RUnjudged{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, o))
