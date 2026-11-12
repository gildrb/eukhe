# eukhe: the proof of LAW headless_exit_budget_limited_zero
#
# PROOF: without the final answer from the reserve, budget_limited is
# false, against the premise (limited); with it, case analysis on the
# facts in the order the model reads them: every failure it does not
# excuse makes budget_limited false; the wait at the deadline, a run and a
# terminal entry the budget refused read on (Hx.excuse); with no other
# failure the model ends budget-limited (hxl.*).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ../base/staging.bend as LStg

def hxl.flags(c: Bool, a: Bool, h: {Bool.and(Bool.not(c), Bool.not(a)) == True{} : Bool}) -> {Hx.by_flags(c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}:
  match c:
    case True{}:
      LStg.stg.absurdF({Hx.by_flags(True{}, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
    case False{}:
      match a:
        case True{}:
          LStg.stg.absurdF({Hx.by_flags(False{}, True{}, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case False{}:
          {==}

def hxl.primary(p: Hx.Primary, c: Bool, a: Bool, h: {Bool.and(HeadlessExit.only_excused(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a))) == True{} : Bool}) -> {Hx.by_primary(p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}:
  match p:
    case Hx.PNothing{}:
      hxl.flags(c, a, h)
    case Hx.PAnswer{}:
      hxl.flags(c, a, h)
    case Hx.PUnfinished{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PUnfinished{}, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
    case Hx.PProviderError{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PProviderError{}, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
    case Hx.PAborted{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PAborted{}, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
    case Hx.PSlashOk{}:
      hxl.flags(c, a, h)
    case Hx.PSlashFailed{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PSlashFailed{}, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
    case Hx.PBudgetRefused{}:
      hxl.flags(c, a, h)

def hxl.run(run: Hx.Run, p: Hx.Primary, c: Bool, a: Bool, h: {Bool.and(HeadlessExit.only_excused(Sp.run_cause(run)), Bool.and(HeadlessExit.only_excused(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a)))) == True{} : Bool}) -> {Hx.by_run(run, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}:
  match run:
    case Hx.NoRun{}:
      hxl.primary(p, c, a, h)
    case Hx.Answered{}:
      hxl.primary(p, c, a, h)
    case Hx.Unanswered{r}:
      match r:
        case Hx.ModelError{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.ModelError{}}, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.RunLimit{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.RunLimit{}}, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.NoModel{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.NoModel{}}, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.ForcedTool{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.ForcedTool{}}, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.Faulted{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.Faulted{}}, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.Aborted{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.Aborted{}}, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.Reset{}:
          hxl.primary(p, c, a, h)
        case Hx.Stale{}:
          hxl.primary(p, c, a, h)
        case Hx.Withdrawn{}:
          hxl.primary(p, c, a, h)
        case Hx.Other{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.Other{}}, p, c, a, True{}) == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.BudgetRefused{}:
          hxl.primary(p, c, a, h)

# the cause is budget-limited
def hxl.cause(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, c: Bool, a: Bool, h: {HeadlessExit.budget_limited(Hx.Facts{cf, w, run, p, c, a, True{}}) == True{} : Bool}) -> {Hx.cause(Hx.Facts{cf, w, run, p, c, a, True{}}) == Hx.CBudgetLimited{} : Hx.Cause}:
  match cf:
    case True{}:
      LStg.stg.absurdF({Hx.CCommandFailed{} == Hx.CBudgetLimited{} : Hx.Cause}, h)
    case False{}:
      match w:
        case Hx.Quiet{}:
          hxl.run(run, p, c, a, h)
        case Hx.GaveUp{}:
          LStg.stg.absurdF({Hx.CGaveUp{} == Hx.CBudgetLimited{} : Hx.Cause}, h)
        case Hx.BudgetDeadline{}:
          hxl.run(run, p, c, a, h)

def HeadlessExit.headless_exit_budget_limited_zero(f, limited):
  match f:
    case Hx.Facts{+cf, +w, +run, +p, +c, +a, ba}:
      match ba:
        case False{}:
          LStg.stg.absurdF({Hx.decide(Hx.Facts{cf, w, run, p, c, a, False{}}) == Hx.Verdict{0n, Hx.CBudgetLimited{}} : Hx.Verdict}, limited)
        case True{}:
          Equal.cong(Hx.Cause, Hx.Verdict, x => Hx.verdict(x), Hx.cause(Hx.Facts{cf, w, run, p, c, a, True{}}), Hx.CBudgetLimited{}, hxl.cause(cf, w, run, p, c, a, limited))
