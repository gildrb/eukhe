# eukhe: lemmas the proofs of area headless_exit share: a failure below
# the command and the wait fails the exit; a failed compaction fails the
# transcript; the cause is E1's first failure, with the failures the
# delivered final answer excuses dropped (hx.cause_eq, against
# Sp.exit_cause); the entry's
# decoder is the laws' reader (spec/durable/headless_wire.bend), stage by
# stage; a spelled request reads back whole

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ../../spec/durable/headless_wire.bend as SpW
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# Failures
# --------

# a run that did not fail leaves the code to the transcript; one that
# failed sets it to 1 (a budget refusal: unless the final answer was
# delivered)
def hx.run_fails(run: Hx.Run, -p: Hx.Primary, -c: Bool, -a: Bool, ba: Bool, h: {Hx.code(Hx.by_primary(p, c, a, ba)) == 1n : Nat}) -> {Hx.code(Hx.by_run(run, p, c, a, ba)) == 1n : Nat}:
  match run:
    case Hx.NoRun{}:
      h
    case Hx.Answered{}:
      h
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
          h
        case Hx.Stale{}:
          h
        case Hx.Withdrawn{}:
          h
        case Hx.Other{}:
          {==}
        case Hx.BudgetRefused{}:
          match ba:
            case True{}:
              h
            case False{}:
              {==}

# a failed command or a give-up exits 1, and the wait at the deadline
# without the final answer; below them the run decides
def hx.facts_fail(cf: Bool, w: Hx.Wait, -run: Hx.Run, -p: Hx.Primary, -c: Bool, -a: Bool, ba: Bool, h: {Hx.code(Hx.by_run(run, p, c, a, ba)) == 1n : Nat}) -> {HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, w, run, p, c, a, ba})) == 1n : Nat}:
  match cf:
    case True{}:
      {==}
    case False{}:
      match w:
        case Hx.Quiet{}:
          h
        case Hx.GaveUp{}:
          {==}
        case Hx.BudgetDeadline{}:
          match ba:
            case True{}:
              h
            case False{}:
              {==}

# whatever the terminal entry, a failed compaction leaves code 1
def hx.comp_fails(p: Hx.Primary, -a: Bool, ba: Bool) -> {Hx.code(Hx.by_primary(p, True{}, a, ba)) == 1n : Nat}:
  match p:
    case Hx.PNothing{}:
      {==}
    case Hx.PAnswer{}:
      {==}
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      {==}
    case Hx.PSlashFailed{}:
      {==}
    case Hx.PBudgetRefused{}:
      match ba:
        case True{}:
          {==}
        case False{}:
          {==}

# The cause
# ---------

# below the transcript, the model's cause is the first of the two flags
def hx.flags_eq(c: Bool, a: Bool, ba: Bool) -> {Hx.by_flags(c, a, ba) == Sp.first([Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})], Sp.unfailed(ba)) : Hx.Cause}:
  match c:
    case True{}:
      {==}
    case False{}:
      match a:
        case True{}:
          {==}
        case False{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}

# below the run, the model's cause is the first of the last three
# failures
def hx.tail(p: Hx.Primary, +c: Bool, +a: Bool, +ba: Bool) -> {Hx.by_primary(p, c, a, ba) == Sp.first([Sp.counts(Sp.primary_cause(p), ba), Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})], Sp.unfailed(ba)) : Hx.Cause}:
  match p:
    case Hx.PNothing{}:
      hx.flags_eq(c, a, ba)
    case Hx.PAnswer{}:
      hx.flags_eq(c, a, ba)
    case Hx.PUnfinished{}:
      match ba:
        case True{}:
          {==}
        case False{}:
          {==}
    case Hx.PProviderError{}:
      match ba:
        case True{}:
          {==}
        case False{}:
          {==}
    case Hx.PAborted{}:
      match ba:
        case True{}:
          {==}
        case False{}:
          {==}
    case Hx.PSlashOk{}:
      hx.flags_eq(c, a, ba)
    case Hx.PSlashFailed{}:
      match ba:
        case True{}:
          {==}
        case False{}:
          {==}
    case Hx.PBudgetRefused{}:
      match ba:
        case True{}:
          hx.flags_eq(c, a, True{})
        case False{}:
          {==}

# below the wait, the model's cause is the first of the last four
# failures
def hx.run_eq(run: Hx.Run, +p: Hx.Primary, +c: Bool, +a: Bool, +ba: Bool) -> {Hx.by_run(run, p, c, a, ba) == Sp.first([Sp.counts(Sp.run_cause(run), ba), Sp.counts(Sp.primary_cause(p), ba), Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})], Sp.unfailed(ba)) : Hx.Cause}:
  match run:
    case Hx.NoRun{}:
      hx.tail(p, c, a, ba)
    case Hx.Answered{}:
      hx.tail(p, c, a, ba)
    case Hx.Unanswered{r}:
      match r:
        case Hx.ModelError{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
        case Hx.RunLimit{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
        case Hx.NoModel{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
        case Hx.ForcedTool{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
        case Hx.Faulted{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
        case Hx.Aborted{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
        case Hx.Reset{}:
          hx.tail(p, c, a, ba)
        case Hx.Stale{}:
          hx.tail(p, c, a, ba)
        case Hx.Withdrawn{}:
          hx.tail(p, c, a, ba)
        case Hx.Other{}:
          match ba:
            case True{}:
              {==}
            case False{}:
              {==}
        case Hx.BudgetRefused{}:
          match ba:
            case True{}:
              hx.tail(p, c, a, True{})
            case False{}:
              {==}

# the model's cause is E1's (Sp.exit_cause)
def hx.cause_eq(f: Hx.Facts) -> {Hx.cause(f) == Sp.exit_cause(f) : Hx.Cause}:
  match f:
    case Hx.Facts{cf, w, +run, +p, +c, +a, +ba}:
      match cf:
        case True{}:
          {==}
        case False{}:
          match w:
            case Hx.Quiet{}:
              hx.run_eq(run, p, c, a, ba)
            case Hx.GaveUp{}:
              match ba:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case Hx.BudgetDeadline{}:
              match ba:
                case True{}:
                  hx.run_eq(run, p, c, a, True{})
                case False{}:
                  {==}

# The reader
# ----------

def hx.wait(d: Wr.Dec<Nat>) -> {FHx.get_wait(d) == SpW.r_wait(d) : Wr.Dec<Hx.Wait>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def hx.reason(d: Wr.Dec<Nat>) -> {FHx.get_reason(d) == SpW.r_reason(d) : Wr.Dec<Hx.Reason>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n:
          {==}
        case 9n:
          {==}
        case 10n:
          {==}
        case 11n+u:
          {==}
    case Wr.Bad{}:
      {==}

def hx.run_reason(d: Wr.Dec<Hx.Reason>) -> {FHx.get_run.reason(d) == SpW.r_run.reason(d) : Wr.Dec<Hx.Run>}:
  match d:
    case Wr.Got{r, s}:
      {==}
    case Wr.Bad{}:
      {==}

def hx.run(d: Wr.Dec<Nat>) -> {FHx.get_run(d) == SpW.r_run(d) : Wr.Dec<Hx.Run>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          %hx.reason(Wr.get_nat(s)) : {FHx.get_run.reason(FHx.get_reason(Wr.get_nat(s))) == SpW.r_run.reason(_) : Wr.Dec<Hx.Run>}
          hx.run_reason(FHx.get_reason(Wr.get_nat(s)))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def hx.primary(d: Wr.Dec<Nat>) -> {FHx.get_primary(d) == SpW.r_primary(d) : Wr.Dec<Hx.Primary>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+u:
          {==}
    case Wr.Bad{}:
      {==}

def hx.budget(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, c: Bool, a: Bool, d: Wr.Dec<Bool>) -> {FHx.get_facts.budget(cf, w, run, p, c, a, d) == SpW.r_exit.budget(cf, w, run, p, c, a, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{ba, s}:
      {==}
    case Wr.Bad{}:
      {==}

def hx.auto(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, c: Bool, d: Wr.Dec<Bool>) -> {FHx.get_facts.auto(cf, w, run, p, c, d) == SpW.r_exit.auto(cf, w, run, p, c, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{a, s}:
      hx.budget(cf, w, run, p, c, a, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def hx.comp(cf: Bool, w: Hx.Wait, run: Hx.Run, p: Hx.Primary, d: Wr.Dec<Bool>) -> {FHx.get_facts.comp(cf, w, run, p, d) == SpW.r_exit.comp(cf, w, run, p, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{c, s}:
      hx.auto(cf, w, run, p, c, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def hx.after_run(cf: Bool, w: Hx.Wait, run: Hx.Run, d: Wr.Dec<Hx.Primary>) -> {FHx.get_facts.primary(cf, w, run, d) == SpW.r_exit.primary(cf, w, run, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{p, s}:
      hx.comp(cf, w, run, p, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def hx.after_wait(+cf: Bool, +w: Hx.Wait, d: Wr.Dec<Hx.Run>) -> {FHx.get_facts.run(cf, w, d) == SpW.r_exit.run(cf, w, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{+run, +s}:
      %hx.primary(Wr.get_nat(s)) : {FHx.get_facts.primary(cf, w, run, FHx.get_primary(Wr.get_nat(s))) == SpW.r_exit.primary(cf, w, run, _) : Wr.Dec<Hx.Facts>}
      hx.after_run(cf, w, run, FHx.get_primary(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def hx.after_command(+cf: Bool, d: Wr.Dec<Hx.Wait>) -> {FHx.get_facts.wait(cf, d) == SpW.r_exit.wait(cf, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{+w, +s}:
      %hx.run(Wr.get_nat(s)) : {FHx.get_facts.run(cf, w, FHx.get_run(Wr.get_nat(s))) == SpW.r_exit.run(cf, w, _) : Wr.Dec<Hx.Facts>}
      hx.after_wait(cf, w, FHx.get_run(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def hx.command(d: Wr.Dec<Bool>) -> {FHx.get_facts.command(d) == SpW.r_exit.command(d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{+cf, +s}:
      %hx.wait(Wr.get_nat(s)) : {FHx.get_facts.wait(cf, FHx.get_wait(Wr.get_nat(s))) == SpW.r_exit.wait(cf, _) : Wr.Dec<Hx.Facts>}
      hx.after_command(cf, FHx.get_wait(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

# the entry reads a request as the laws' reader does
def hx.req(+s: String) -> {FHx.get_facts(s) == SpW.r_exit(s) : Wr.Dec<Hx.Facts>}:
  hx.command(Wr.get_bool(s))

# Read back
# ---------

def hx.reason_rt(r: Hx.Reason, -rest: String) -> {SpW.r_reason(Wr.get_nat(SpW.w_reason(r, rest))) == Wr.Got{r, rest} : Wr.Dec<Hx.Reason>}:
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
      {==}
    case Hx.Stale{}:
      {==}
    case Hx.Withdrawn{}:
      {==}
    case Hx.Other{}:
      {==}
    case Hx.BudgetRefused{}:
      {==}

def hx.wait_rt(w: Hx.Wait, -rest: String) -> {SpW.r_wait(Wr.get_nat(SpW.w_wait(w, rest))) == Wr.Got{w, rest} : Wr.Dec<Hx.Wait>}:
  match w:
    case Hx.Quiet{}:
      {==}
    case Hx.GaveUp{}:
      {==}
    case Hx.BudgetDeadline{}:
      {==}

def hx.run_rt(run: Hx.Run, +rest: String) -> {SpW.r_run(Wr.get_nat(SpW.w_run(run, rest))) == Wr.Got{run, rest} : Wr.Dec<Hx.Run>}:
  match run:
    case Hx.NoRun{}:
      {==}
    case Hx.Answered{}:
      {==}
    case Hx.Unanswered{+r}:
      %Equal.sym(Wr.Dec<Hx.Reason>, SpW.r_reason(Wr.get_nat(SpW.w_reason(r, rest))), Wr.Got{r, rest}, hx.reason_rt(r, rest)) : {SpW.r_run.reason(_) == Wr.Got{Hx.Unanswered{r}, rest} : Wr.Dec<Hx.Run>}
      {==}

def hx.primary_rt(p: Hx.Primary, -rest: String) -> {SpW.r_primary(Wr.get_nat(SpW.w_primary(p, rest))) == Wr.Got{p, rest} : Wr.Dec<Hx.Primary>}:
  match p:
    case Hx.PNothing{}:
      {==}
    case Hx.PAnswer{}:
      {==}
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      {==}
    case Hx.PSlashFailed{}:
      {==}
    case Hx.PBudgetRefused{}:
      {==}

# a spelled request reads back (with the laws' reader), and the rest is
# untouched
def hx.req_rt(+f: Hx.Facts, +rest: String) -> {SpW.r_exit(SpW.w_exit_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Hx.Facts>}:
  match f:
    case Hx.Facts{+cf, +w, +run, +p, +c, +a, +ba}:
      +r7 = Wr.put_bool(ba, rest)
      +r6 = Wr.put_bool(a, r7)
      +r5 = Wr.put_bool(c, r6)
      +r4 = SpW.w_primary(p, r5)
      +r3 = SpW.w_run(run, r4)
      +r2 = SpW.w_wait(w, r3)
      -g = {Wr.Got{Hx.Facts{cf, w, run, p, c, a, ba}, rest} : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(cf, r2)), Wr.Got{cf, r2}, Wire.wire_bool_round_trip(cf, r2)) : {SpW.r_exit.command(_) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Hx.Wait>, SpW.r_wait(Wr.get_nat(r2)), Wr.Got{w, r3}, hx.wait_rt(w, r3)) : {SpW.r_exit.wait(cf, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Hx.Run>, SpW.r_run(Wr.get_nat(r3)), Wr.Got{run, r4}, hx.run_rt(run, r4)) : {SpW.r_exit.run(cf, w, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Hx.Primary>, SpW.r_primary(Wr.get_nat(r4)), Wr.Got{p, r5}, hx.primary_rt(p, r5)) : {SpW.r_exit.primary(cf, w, run, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r5), Wr.Got{c, r6}, Wire.wire_bool_round_trip(c, r6)) : {SpW.r_exit.comp(cf, w, run, p, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r6), Wr.Got{a, r7}, Wire.wire_bool_round_trip(a, r7)) : {SpW.r_exit.auto(cf, w, run, p, c, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r7), Wr.Got{ba, rest}, Wire.wire_bool_round_trip(ba, rest)) : {SpW.r_exit.budget(cf, w, run, p, c, a, _) == g : Wr.Dec<Hx.Facts>}
      {==}
