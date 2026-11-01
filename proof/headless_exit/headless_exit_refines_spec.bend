# eukhe: the proof of LAW headless_exit_refines_spec
#
# PROOF: the model's cause is the spec's (hx.cause_eq), and the model's exit of a cause is the spec's code of it with the cause (hx.verdict_eq).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ./base.bend as LAHeadlessExit

def hx.verdict_eq(x: Hx.Cause) -> {Hx.verdict(x) == Hx.Verdict{Sp.code_spec(Sp.answered(x)), x} : Hx.Verdict}:
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

def HeadlessExit.headless_exit_refines_spec(f):
  %Equal.sym(Hx.Cause, Hx.cause(f), Sp.cause_spec(f), LAHeadlessExit.hx.cause_eq(f)) : {Hx.verdict(_) == Sp.exit_spec(f) : Hx.Verdict}
  hx.verdict_eq(Sp.cause_spec(f))
