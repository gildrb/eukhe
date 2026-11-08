# eukhe: the proof of LAW headless_exit_zero_iff_answered
#
# PROOF: the code of every cause is 0 exactly for an answered run (hx.zero).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp

def hx.zero(x: Hx.Cause) -> {Nat.is_eq(Hx.code(x), 0n) == Sp.answered(x) : Bool}:
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

def HeadlessExit.headless_exit_zero_iff_answered(f):
  hx.zero(Hx.cause(f))
