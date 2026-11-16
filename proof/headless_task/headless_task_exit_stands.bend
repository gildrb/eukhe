# eukhe: the proof of LAW headless_task_exit_stands
#
# PROOF: case analysis on the cause and the goal: every pair but an answer with its goal open computes to the exit of its cause, standing; that pair contradicts the premise.

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

def HeadlessTask.headless_task_exit_stands(f, h):
  match f:
    case Ht.Facts{c, g}:
      match c:
        case Hx.CAnswered{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              LLogicLogic.absurd({Ht.decide(Ht.Facts{Hx.CAnswered{}, Ht.Open{}}) == Ht.Verdict{Hx.code(SpT.cause_of(Ht.Facts{Hx.CAnswered{}, Ht.Open{}})), Ht.Stands{}} : Ht.Verdict}, Equal.sym(Bool, True{}, False{}, h))
        case Hx.CCommandFailed{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CGaveUp{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CRunFailed{r}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CProviderError{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CAborted{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CUnfinished{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CSlashFailed{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CCompactionFailed{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CAutonomousFailed{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CBudgetLimited{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
        case Hx.CBudgetUnanswered{}:
          match g:
            case Ht.NoGoal{}:
              {==}
            case Ht.Complete{}:
              {==}
            case Ht.Open{}:
              {==}
