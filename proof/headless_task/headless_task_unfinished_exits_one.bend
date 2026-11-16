# eukhe: the proof of LAW headless_task_unfinished_exits_one
#
# PROOF: case analysis on the cause and the goal: an answer with its goal open computes to exit 1 incomplete; every other pair contradicts the premise.

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

def HeadlessTask.headless_task_unfinished_exits_one(f, h):
  match f:
    case Ht.Facts{c, g}:
      match c:
        case Hx.CAnswered{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              {==}
        case Hx.CCommandFailed{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCommandFailed{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CGaveUp{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CGaveUp{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CRunFailed{r}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{r}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{r}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CRunFailed{r}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CProviderError{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CProviderError{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CAborted{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAborted{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CUnfinished{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CUnfinished{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CSlashFailed{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CSlashFailed{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CCompactionFailed{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CCompactionFailed{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CAutonomousFailed{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAutonomousFailed{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CBudgetLimited{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetLimited{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
        case Hx.CBudgetUnanswered{}:
          match g:
            case Ht.NoGoal{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.NoGoal{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Complete{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Complete{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CBudgetUnanswered{}, Ht.Open{}}) == Ht.Verdict{1n, Ht.Incomplete{}} : Ht.Verdict}, h)
