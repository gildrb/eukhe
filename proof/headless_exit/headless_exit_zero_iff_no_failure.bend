# eukhe: the proof of LAW headless_exit_zero_iff_no_failure
#
# PROOF: case analysis on the facts in the order the model reads them: a
# failed command or a give-up gives code 1 and makes no_failure false; a
# run that failed gives 1 and its run_cause holds (hxz.run); below the run,
# a failed terminal entry gives 1 and its primary_cause holds (hxz.primary);
# below the entry, the two flags give 0 exactly when neither holds
# (hxz.flags).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp

def hxz.flags(c: Bool, a: Bool) -> {Nat.is_eq(Hx.code(Hx.by_flags(c, a)), 0n) == Bool.and(Bool.not(c), Bool.not(a)) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      match a:
        case True{}:
          {==}
        case False{}:
          {==}

def hxz.primary(p: Hx.Primary, c: Bool, a: Bool) -> {Nat.is_eq(Hx.code(Hx.by_primary(p, c, a)), 0n) == Bool.and(HeadlessExit.holds_not(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a))) : Bool}:
  match p:
    case Hx.PNothing{}:
      hxz.flags(c, a)
    case Hx.PAnswer{}:
      hxz.flags(c, a)
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      hxz.flags(c, a)
    case Hx.PSlashFailed{}:
      {==}

def hxz.run(run: Hx.Run, p: Hx.Primary, c: Bool, a: Bool) -> {Nat.is_eq(Hx.code(Hx.by_run(run, p, c, a)), 0n) == Bool.and(HeadlessExit.holds_not(Sp.run_cause(run)), Bool.and(HeadlessExit.holds_not(Sp.primary_cause(p)), Bool.and(Bool.not(c), Bool.not(a)))) : Bool}:
  match run:
    case Hx.NoRun{}:
      hxz.primary(p, c, a)
    case Hx.Answered{}:
      hxz.primary(p, c, a)
    case Hx.Unanswered{r}:
      match r:
        case Hx.ModelError{}:
          {==}
        case Hx.RunLimit{}:
          {==}
        case Hx.NoModel{}:
          {==}
        case Hx.ForcedTool{}:
          {==}
        case Hx.Faulted{}:
          {==}
        case Hx.Aborted{}:
          {==}
        case Hx.Reset{}:
          hxz.primary(p, c, a)
        case Hx.Stale{}:
          hxz.primary(p, c, a)
        case Hx.Withdrawn{}:
          hxz.primary(p, c, a)
        case Hx.Other{}:
          {==}

def HeadlessExit.headless_exit_zero_iff_no_failure(f):
  match f:
    case Hx.Facts{cf, gu, run, p, c, a}:
      match cf:
        case True{}:
          {==}
        case False{}:
          match gu:
            case True{}:
              {==}
            case False{}:
              hxz.run(run, p, c, a)
