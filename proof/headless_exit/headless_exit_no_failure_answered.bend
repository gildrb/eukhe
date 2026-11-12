# eukhe: the proof of LAW headless_exit_no_failure_answered
#
# PROOF: case analysis on the facts in the order the model reads them;
# every failure fact makes no_failure false, against the premise (clean);
# with none the model falls through every check to an answered run.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ../base/staging.bend as LStg

def hxa.flags(c: Bool, a: Bool, h: {Bool.and(Bool.not(c), Bool.not(a)) == True{} : Bool}) -> {Hx.by_flags(c, a) == Hx.CAnswered{} : Hx.Cause}:
  match c:
    case True{}:
      LStg.stg.absurdF({Hx.by_flags(True{}, a) == Hx.CAnswered{} : Hx.Cause}, h)
    case False{}:
      match a:
        case True{}:
          LStg.stg.absurdF({Hx.by_flags(False{}, True{}) == Hx.CAnswered{} : Hx.Cause}, h)
        case False{}:
          {==}

def hxa.primary(p: Hx.Primary, c: Bool, a: Bool, h: {Bool.and(HeadlessExit.holds_not(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a))) == True{} : Bool}) -> {Hx.by_primary(p, c, a) == Hx.CAnswered{} : Hx.Cause}:
  match p:
    case Hx.PNothing{}:
      hxa.flags(c, a, h)
    case Hx.PAnswer{}:
      hxa.flags(c, a, h)
    case Hx.PUnfinished{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PUnfinished{}, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
    case Hx.PProviderError{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PProviderError{}, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
    case Hx.PAborted{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PAborted{}, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
    case Hx.PSlashOk{}:
      hxa.flags(c, a, h)
    case Hx.PSlashFailed{}:
      LStg.stg.absurdF({Hx.by_primary(Hx.PSlashFailed{}, c, a) == Hx.CAnswered{} : Hx.Cause}, h)

def hxa.run(run: Hx.Run, p: Hx.Primary, c: Bool, a: Bool, h: {Bool.and(HeadlessExit.holds_not(Sp.run_cause(run)), Bool.and(HeadlessExit.holds_not(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a)))) == True{} : Bool}) -> {Hx.by_run(run, p, c, a) == Hx.CAnswered{} : Hx.Cause}:
  match run:
    case Hx.NoRun{}:
      hxa.primary(p, c, a, h)
    case Hx.Answered{}:
      hxa.primary(p, c, a, h)
    case Hx.Unanswered{r}:
      match r:
        case Hx.ModelError{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.ModelError{}}, p, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
        case Hx.RunLimit{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.RunLimit{}}, p, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
        case Hx.NoModel{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.NoModel{}}, p, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
        case Hx.ForcedTool{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.ForcedTool{}}, p, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
        case Hx.Faulted{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.Faulted{}}, p, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
        case Hx.Aborted{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.Aborted{}}, p, c, a) == Hx.CAnswered{} : Hx.Cause}, h)
        case Hx.Reset{}:
          hxa.primary(p, c, a, h)
        case Hx.Stale{}:
          hxa.primary(p, c, a, h)
        case Hx.Withdrawn{}:
          hxa.primary(p, c, a, h)
        case Hx.Other{}:
          LStg.stg.absurdF({Hx.by_run(Hx.Unanswered{Hx.Other{}}, p, c, a) == Hx.CAnswered{} : Hx.Cause}, h)

def HeadlessExit.headless_exit_no_failure_answered(f, clean):
  match f:
    case Hx.Facts{cf, gu, run, p, c, a}:
      match cf:
        case True{}:
          LStg.stg.absurdF({Hx.CCommandFailed{} == Hx.CAnswered{} : Hx.Cause}, clean)
        case False{}:
          match gu:
            case True{}:
              LStg.stg.absurdF({Hx.CGaveUp{} == Hx.CAnswered{} : Hx.Cause}, clean)
            case False{}:
              hxa.run(run, p, c, a, clean)
