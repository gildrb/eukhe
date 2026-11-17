# eukhe: the proof of LAW headless_exit_zero_iff_no_failure
#
# PROOF: case analysis on the final answer from the reserve, then on the
# facts in the order the model reads them. Without that answer
# budget_limited is false (hxz.or_false), and as before the rule: a
# failed command, a give-up or the wait at the deadline gives code 1 and
# makes no_failure false; a run that failed gives 1 and its run_cause
# holds (hxz.run); below the run, a failed terminal entry gives 1 and its
# primary_cause holds (hxz.primary); below the entry, the compaction
# flag gives 0 exactly when it does not hold (hxz.flags). With that
# answer no_failure implies budget_limited (hxz.or_x), and the code is 0
# exactly when only failures it excuses hold (hxzb.*).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp

def hxz.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Without the final answer from the reserve
# -----------------------------------------

def hxz.flags(c: Bool) -> {Nat.is_eq(Hx.code(Hx.by_flags(c, False{})), 0n) == Bool.not(c) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def hxz.primary(p: Hx.Primary, c: Bool) -> {Nat.is_eq(Hx.code(Hx.by_primary(p, c, False{})), 0n) == Bool.and(HeadlessExit.holds_not(Sp.primary_cause(p)), Bool.not(c)) : Bool}:
  match p:
    case Hx.PNothing{}:
      hxz.flags(c)
    case Hx.PAnswer{}:
      hxz.flags(c)
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      hxz.flags(c)
    case Hx.PSlashFailed{}:
      {==}
    case Hx.PBudgetRefused{}:
      {==}

def hxz.run(run: Hx.Run, p: Hx.Primary, c: Bool) -> {Nat.is_eq(Hx.code(Hx.by_run(run, p, c, False{})), 0n) == Bool.and(HeadlessExit.holds_not(Sp.run_cause(run)), Bool.and(HeadlessExit.holds_not(Sp.primary_cause(p)), Bool.not(c))) : Bool}:
  match run:
    case Hx.NoRun{}:
      hxz.primary(p, c)
    case Hx.Answered{}:
      hxz.primary(p, c)
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
          hxz.primary(p, c)
        case Hx.Stale{}:
          hxz.primary(p, c)
        case Hx.Withdrawn{}:
          hxz.primary(p, c)
        case Hx.Other{}:
          {==}
        case Hx.BudgetRefused{}:
          {==}

def hxz.plain(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, c: Bool) -> {Nat.is_eq(HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, run, p, c, False{}})), 0n) == HeadlessExit.no_failure(Hx.Facts{cf, w, run, p, c, False{}}) : Bool}:
  match cf:
    case True{}:
      {==}
    case False{}:
      match w:
        case Hx.Quiet{}:
          hxz.run(run, p, c)
        case Hx.GaveUp{}:
          {==}
        case Hx.BudgetDeadline{}:
          {==}

# With the final answer from the reserve
# --------------------------------------

def hxzb.flags(c: Bool) -> {Nat.is_eq(Hx.code(Hx.by_flags(c, True{})), 0n) == Bool.not(c) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def hxzb.primary(p: Hx.Primary, c: Bool) -> {Nat.is_eq(Hx.code(Hx.by_primary(p, c, True{})), 0n) == Bool.and(HeadlessExit.only_excused(Sp.primary_cause(p)), Bool.not(c)) : Bool}:
  match p:
    case Hx.PNothing{}:
      hxzb.flags(c)
    case Hx.PAnswer{}:
      hxzb.flags(c)
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      hxzb.flags(c)
    case Hx.PSlashFailed{}:
      {==}
    case Hx.PBudgetRefused{}:
      hxzb.flags(c)

def hxzb.run(run: Hx.Run, p: Hx.Primary, c: Bool) -> {Nat.is_eq(Hx.code(Hx.by_run(run, p, c, True{})), 0n) == Bool.and(HeadlessExit.only_excused(Sp.run_cause(run)), Bool.and(HeadlessExit.only_excused(Sp.primary_cause(p)), Bool.not(c))) : Bool}:
  match run:
    case Hx.NoRun{}:
      hxzb.primary(p, c)
    case Hx.Answered{}:
      hxzb.primary(p, c)
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
          hxzb.primary(p, c)
        case Hx.Stale{}:
          hxzb.primary(p, c)
        case Hx.Withdrawn{}:
          hxzb.primary(p, c)
        case Hx.Other{}:
          {==}
        case Hx.BudgetRefused{}:
          hxzb.primary(p, c)

def hxzb.budget(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, c: Bool) -> {Nat.is_eq(HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, run, p, c, True{}})), 0n) == HeadlessExit.budget_limited(Hx.Facts{cf, w, run, p, c, True{}}) : Bool}:
  match cf:
    case True{}:
      {==}
    case False{}:
      match w:
        case Hx.Quiet{}:
          hxzb.run(run, p, c)
        case Hx.GaveUp{}:
          {==}
        case Hx.BudgetDeadline{}:
          hxzb.run(run, p, c)

# with the final answer, no failure is budget-limited: the disjunction is
# budget_limited
def hxz.step(m: Maybe<&2, Hx.Cause>, -n: Bool, -x: Bool, h: {Bool.or(n, x) == x : Bool}) -> {Bool.or(Bool.and(HeadlessExit.holds_not(m), n), Bool.and(HeadlessExit.only_excused(m), x)) == Bool.and(HeadlessExit.only_excused(m), x) : Bool}:
  match m:
    case None{}:
      h
    case Some{y}:
      {==}

def hxz.flags_or(c: Bool) -> {Bool.or(Bool.not(c), Bool.not(c)) == Bool.not(c) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def hxz.or_x(cf: Bool, +w: Hx.Wait, +run: Hx.Run, +p: Hx.Primary, +c: Bool) -> {Bool.or(HeadlessExit.no_failure(Hx.Facts{cf, w, run, p, c, True{}}), HeadlessExit.budget_limited(Hx.Facts{cf, w, run, p, c, True{}})) == HeadlessExit.budget_limited(Hx.Facts{cf, w, run, p, c, True{}}) : Bool}:
  match cf:
    case True{}:
      {==}
    case False{}:
      +fl = Bool.not(c)
      +pn = Bool.and(HeadlessExit.holds_not(Sp.primary_cause(p)), fl)
      +px = Bool.and(HeadlessExit.only_excused(Sp.primary_cause(p)), fl)
      +rn = Bool.and(HeadlessExit.holds_not(Sp.run_cause(run)), pn)
      +rx = Bool.and(HeadlessExit.only_excused(Sp.run_cause(run)), px)
      hxz.step(Sp.wait_cause(w), rn, rx, hxz.step(Sp.run_cause(run), pn, px, hxz.step(Sp.primary_cause(p), fl, fl, hxz.flags_or(c))))

def HeadlessExit.headless_exit_zero_iff_no_failure(f):
  match f:
    case Hx.Facts{+cf, +w, +run, +p, +c, ba}:
      match ba:
        case False{}:
          +nf = HeadlessExit.no_failure(Hx.Facts{cf, w, run, p, c, False{}})
          %Equal.sym(Bool, Bool.or(nf, False{}), nf, hxz.or_false(nf)) : {Nat.is_eq(HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, run, p, c, False{}})), 0n) == _ : Bool}
          hxz.plain(cf, w, run, p, c)
        case True{}:
          +bl = HeadlessExit.budget_limited(Hx.Facts{cf, w, run, p, c, True{}})
          %Equal.sym(Bool, Bool.or(HeadlessExit.no_failure(Hx.Facts{cf, w, run, p, c, True{}}), bl), bl, hxz.or_x(cf, w, run, p, c)) : {Nat.is_eq(HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, run, p, c, True{}})), 0n) == _ : Bool}
          hxzb.budget(cf, w, run, p, c)
