# eukhe: the proof of LAW headless_task_unjudged_iff_unread
#
# PROOF: case analysis on the cause, the goal, the acted fact and the reading: each side computes.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../spec/durable/headless_task.bend as SpT
import ../../laws/headless_task.bend as HeadlessTask

def HeadlessTask.headless_task_unjudged_iff_unread(f):
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
        case Hx.CCommandFailed{}:
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
          match g:
            case Ht.NoGoal{}:
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
            case Ht.Complete{}:
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
            case Ht.Open{}:
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
