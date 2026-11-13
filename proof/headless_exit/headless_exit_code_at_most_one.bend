# eukhe: the proof of LAW headless_exit_code_at_most_one
#
# PROOF: the code of every cause is 0 or 1 (hx.small).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit

def hx.small(x: Hx.Cause) -> {Nat.is_le(Hx.code(x), 1n) == True{} : Bool}:
  match x:
    case Hx.CAnswered{}:
      {==}
    case Hx.CCommandFailed{}:
      {==}
    case Hx.CGaveUp{}:
      {==}
    case Hx.CRunFailed{r}:
      {==}
    case Hx.CProviderError{}:
      {==}
    case Hx.CAborted{}:
      {==}
    case Hx.CUnfinished{}:
      {==}
    case Hx.CSlashFailed{}:
      {==}
    case Hx.CCompactionFailed{}:
      {==}
    case Hx.CAutonomousFailed{}:
      {==}
    case Hx.CBudgetLimited{}:
      {==}
    case Hx.CBudgetUnanswered{}:
      {==}

def HeadlessExit.headless_exit_code_at_most_one(f):
  hx.small(Hx.cause(f))
