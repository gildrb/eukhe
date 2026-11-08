# eukhe: lemmas the proofs of area headless_exit share: a failure below
# the command and the wait fails the exit; the cause is the first failure
# of the list of E1 (hx.cause_eq, a proof step, not a spec); the entry's
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
# failed sets it to 1
def hx.run_fails(run: Hx.Run, -p: Hx.Primary, -c: Bool, -a: Bool, h: {Hx.code(Hx.by_primary(p, c, a)) == 1n : Nat}) -> {Hx.code(Hx.by_run(run, p, c, a)) == 1n : Nat}:
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

# a failed command or a give-up exits 1; below them the run decides
def hx.facts_fail(cf: Bool, gu: Bool, -run: Hx.Run, -p: Hx.Primary, -c: Bool, -a: Bool, h: {Hx.code(Hx.by_run(run, p, c, a)) == 1n : Nat}) -> {HeadlessExit.code_of(Hx.decide(Hx.Facts{cf, gu, run, p, c, a})) == 1n : Nat}:
  match cf:
    case True{}:
      {==}
    case False{}:
      match gu:
        case True{}:
          {==}
        case False{}:
          h

# The cause
# ---------

# the first failure of the list, else answered
def hx.first(xs: List<&2, Maybe<&2, Hx.Cause>>) -> Hx.Cause:
  match xs:
    case Nil{}:
      Hx.CAnswered{}
    case Con{m, rest}:
      match m:
        case None{}:
          hx.first(rest)
        case Some{c}:
          c

# the failures in the order of E1
def hx.failures(f: Hx.Facts) -> List<&2, Maybe<&2, Hx.Cause>>:
  match f:
    case Hx.Facts{cf, gu, run, p, c, a}:
      [Sp.when(cf, Hx.CCommandFailed{}), Sp.when(gu, Hx.CGaveUp{}), Sp.run_cause(run), Sp.primary_cause(p), Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})]

# the first failure of the facts, in the order of E1
def hx.cause_spec(f: Hx.Facts) -> Hx.Cause:
  hx.first(hx.failures(f))

# below the run, the model's cause is the first of the last three
# failures
def hx.tail(p: Hx.Primary, c: Bool, a: Bool) -> {Hx.by_primary(p, c, a) == hx.first([Sp.primary_cause(p), Sp.when(c, Hx.CCompactionFailed{}), Sp.when(a, Hx.CAutonomousFailed{})]) : Hx.Cause}:
  match p:
    case Hx.PNothing{}:
      match c:
        case True{}:
          {==}
        case False{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
    case Hx.PAnswer{}:
      match c:
        case True{}:
          {==}
        case False{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
    case Hx.PUnfinished{}:
      {==}
    case Hx.PProviderError{}:
      {==}
    case Hx.PAborted{}:
      {==}
    case Hx.PSlashOk{}:
      match c:
        case True{}:
          {==}
        case False{}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
    case Hx.PSlashFailed{}:
      {==}

# the model's cause is the first failure of the facts
def hx.cause_eq(f: Hx.Facts) -> {Hx.cause(f) == hx.cause_spec(f) : Hx.Cause}:
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
              match run:
                case Hx.NoRun{}:
                  hx.tail(p, c, a)
                case Hx.Answered{}:
                  hx.tail(p, c, a)
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
                      hx.tail(p, c, a)
                    case Hx.Stale{}:
                      hx.tail(p, c, a)
                    case Hx.Withdrawn{}:
                      hx.tail(p, c, a)
                    case Hx.Other{}:
                      {==}

# The reader
# ----------

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
        case 10n+u:
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
        case 7n+u:
          {==}
    case Wr.Bad{}:
      {==}

def hx.auto(cf: Bool, gu: Bool, run: Hx.Run, p: Hx.Primary, c: Bool, d: Wr.Dec<Bool>) -> {FHx.get_facts.auto(cf, gu, run, p, c, d) == SpW.r_exit.auto(cf, gu, run, p, c, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def hx.comp(cf: Bool, gu: Bool, run: Hx.Run, p: Hx.Primary, d: Wr.Dec<Bool>) -> {FHx.get_facts.comp(cf, gu, run, p, d) == SpW.r_exit.comp(cf, gu, run, p, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{c, s}:
      hx.auto(cf, gu, run, p, c, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def hx.after_run(cf: Bool, gu: Bool, run: Hx.Run, d: Wr.Dec<Hx.Primary>) -> {FHx.get_facts.primary(cf, gu, run, d) == SpW.r_exit.primary(cf, gu, run, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{p, s}:
      hx.comp(cf, gu, run, p, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def hx.after_gave_up(+cf: Bool, +gu: Bool, d: Wr.Dec<Hx.Run>) -> {FHx.get_facts.run(cf, gu, d) == SpW.r_exit.run(cf, gu, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{+run, +s}:
      %hx.primary(Wr.get_nat(s)) : {FHx.get_facts.primary(cf, gu, run, FHx.get_primary(Wr.get_nat(s))) == SpW.r_exit.primary(cf, gu, run, _) : Wr.Dec<Hx.Facts>}
      hx.after_run(cf, gu, run, FHx.get_primary(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def hx.after_command(+cf: Bool, d: Wr.Dec<Bool>) -> {FHx.get_facts.gave_up(cf, d) == SpW.r_exit.gave_up(cf, d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{+gu, +s}:
      %hx.run(Wr.get_nat(s)) : {FHx.get_facts.run(cf, gu, FHx.get_run(Wr.get_nat(s))) == SpW.r_exit.run(cf, gu, _) : Wr.Dec<Hx.Facts>}
      hx.after_gave_up(cf, gu, FHx.get_run(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def hx.command(d: Wr.Dec<Bool>) -> {FHx.get_facts.command(d) == SpW.r_exit.command(d) : Wr.Dec<Hx.Facts>}:
  match d:
    case Wr.Got{cf, s}:
      hx.after_command(cf, Wr.get_bool(s))
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

# a spelled request reads back (with the laws' reader), and the rest is
# untouched
def hx.req_rt(+f: Hx.Facts, +rest: String) -> {SpW.r_exit(SpW.w_exit_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Hx.Facts>}:
  match f:
    case Hx.Facts{+cf, +gu, +run, +p, +c, +a}:
      +r6 = Wr.put_bool(a, rest)
      +r5 = Wr.put_bool(c, r6)
      +r4 = SpW.w_primary(p, r5)
      +r3 = SpW.w_run(run, r4)
      +r2 = Wr.put_bool(gu, r3)
      -g = {Wr.Got{Hx.Facts{cf, gu, run, p, c, a}, rest} : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(cf, r2)), Wr.Got{cf, r2}, Wire.wire_bool_round_trip(cf, r2)) : {SpW.r_exit.command(_) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r2), Wr.Got{gu, r3}, Wire.wire_bool_round_trip(gu, r3)) : {SpW.r_exit.gave_up(cf, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Hx.Run>, SpW.r_run(Wr.get_nat(r3)), Wr.Got{run, r4}, hx.run_rt(run, r4)) : {SpW.r_exit.run(cf, gu, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Hx.Primary>, SpW.r_primary(Wr.get_nat(r4)), Wr.Got{p, r5}, hx.primary_rt(p, r5)) : {SpW.r_exit.primary(cf, gu, run, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r5), Wr.Got{c, r6}, Wire.wire_bool_round_trip(c, r6)) : {SpW.r_exit.comp(cf, gu, run, p, _) == g : Wr.Dec<Hx.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r6), Wr.Got{a, rest}, Wire.wire_bool_round_trip(a, rest)) : {SpW.r_exit.auto(cf, gu, run, p, c, _) == g : Wr.Dec<Hx.Facts>}
      {==}
