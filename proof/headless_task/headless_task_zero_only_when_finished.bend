# eukhe: the proof of LAW headless_task_zero_only_when_finished
#
# PROOF: case analysis on the cause, the acted fact and the reading: each side computes.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../spec/durable/headless_task.bend as SpT
import ../../laws/headless_task.bend as HeadlessTask

def HeadlessTask.headless_task_zero_only_when_finished(f):
  match f:
    case Ht.Facts{c, a, r}:
      match c:
        case Hx.CAnswered{}:
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
