# eukhe: the proof of LAW headless_exit_code_zero_iff_success
#
# PROOF: case by case on the cause: each side computes (a run failed for
# any reason has code 1).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit

def HeadlessExit.headless_exit_code_zero_iff_success(c):
  match c:
    case Hx.CAnswered{}:
      ({==}, {==})
    case Hx.CCommandFailed{}:
      ({==}, {==})
    case Hx.CGaveUp{}:
      ({==}, {==})
    case Hx.CRunFailed{r}:
      ({==}, {==})
    case Hx.CProviderError{}:
      ({==}, {==})
    case Hx.CAborted{}:
      ({==}, {==})
    case Hx.CUnfinished{}:
      ({==}, {==})
    case Hx.CSlashFailed{}:
      ({==}, {==})
    case Hx.CCompactionFailed{}:
      ({==}, {==})
    case Hx.CBudgetLimited{}:
      ({==}, {==})
    case Hx.CBudgetUnanswered{}:
      ({==}, {==})
