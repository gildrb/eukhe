# eukhe: lemmas the proofs of area headless_task share: the entry's
# decoder is the laws' reader (spec/durable/headless_task.bend), stage by
# stage; a spelled request reads back whole; the entry spells a task's
# exit as the spec does

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../spec/durable/headless_task.bend as SpT
import ../../laws/headless_task.bend as HeadlessTask

# The reader
# ----------

def ht.reason(d: Wr.Dec<Nat>) -> {FHx.get_reason(d) == SpW.r_reason(d) : Wr.Dec<Hx.Reason>}:
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

def ht.failed(d: Wr.Dec<Hx.Reason>) -> {FHt.get_cause.failed(d) == SpT.r_cause.failed(d) : Wr.Dec<Hx.Cause>}:
  match d:
    case Wr.Got{r, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ht.cause(d: Wr.Dec<Nat>) -> {FHt.get_cause(d) == SpT.r_cause(d) : Wr.Dec<Hx.Cause>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          %ht.reason(Wr.get_nat(s)) : {FHt.get_cause.failed(FHx.get_reason(Wr.get_nat(s))) == SpT.r_cause.failed(_) : Wr.Dec<Hx.Cause>}
          ht.failed(FHx.get_reason(Wr.get_nat(s)))
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
        case 11n:
          {==}
        case 12n+u:
          {==}
    case Wr.Bad{}:
      {==}

def ht.goal(d: Wr.Dec<Nat>) -> {FHt.get_goal(d) == SpT.r_goal(d) : Wr.Dec<Ht.Goal>}:
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

def ht.after_cause(c: Hx.Cause, d: Wr.Dec<Ht.Goal>) -> {FHt.get_facts.goal(c, d) == SpT.r_task.goal(c, d) : Wr.Dec<Ht.Facts>}:
  match d:
    case Wr.Got{g, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ht.after_reason(d: Wr.Dec<Hx.Cause>) -> {FHt.get_facts.cause(d) == SpT.r_task.cause(d) : Wr.Dec<Ht.Facts>}:
  match d:
    case Wr.Got{+c, +s}:
      %ht.goal(Wr.get_nat(s)) : {FHt.get_facts.goal(c, FHt.get_goal(Wr.get_nat(s))) == SpT.r_task.goal(c, _) : Wr.Dec<Ht.Facts>}
      ht.after_cause(c, FHt.get_goal(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

# the entry reads a request as the laws' reader does
def ht.req(+s: String) -> {FHt.get_facts(s) == SpT.r_task(s) : Wr.Dec<Ht.Facts>}:
  %ht.cause(Wr.get_nat(s)) : {FHt.get_facts.cause(FHt.get_cause(Wr.get_nat(s))) == SpT.r_task.cause(_) : Wr.Dec<Ht.Facts>}
  ht.after_reason(FHt.get_cause(Wr.get_nat(s)))

# Read back
# ---------

def ht.reason_rt(r: Hx.Reason, -rest: String) -> {SpW.r_reason(Wr.get_nat(SpW.w_reason(r, rest))) == Wr.Got{r, rest} : Wr.Dec<Hx.Reason>}:
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

def ht.cause_rt(c: Hx.Cause, +rest: String) -> {SpT.r_cause(Wr.get_nat(SpW.w_cause(c, rest))) == Wr.Got{c, rest} : Wr.Dec<Hx.Cause>}:
  match c:
    case Hx.CAnswered{}:
      {==}
    case Hx.CCommandFailed{}:
      {==}
    case Hx.CGaveUp{}:
      {==}
    case Hx.CRunFailed{+r}:
      %Equal.sym(Wr.Dec<Hx.Reason>, SpW.r_reason(Wr.get_nat(SpW.w_reason(r, rest))), Wr.Got{r, rest}, ht.reason_rt(r, rest)) : {SpT.r_cause.failed(_) == Wr.Got{Hx.CRunFailed{r}, rest} : Wr.Dec<Hx.Cause>}
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

def ht.goal_rt(g: Ht.Goal, -rest: String) -> {SpT.r_goal(Wr.get_nat(SpT.w_goal(g, rest))) == Wr.Got{g, rest} : Wr.Dec<Ht.Goal>}:
  match g:
    case Ht.NoGoal{}:
      {==}
    case Ht.Complete{}:
      {==}
    case Ht.Open{}:
      {==}

# a spelled request reads back (with the laws' reader), and the rest is
# untouched
def ht.req_rt(+f: Ht.Facts, +rest: String) -> {SpT.r_task(SpT.w_task_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Ht.Facts>}:
  match f:
    case Ht.Facts{+c, +g}:
      +r1 = SpT.w_goal(g, rest)
      -q = {Wr.Got{Ht.Facts{c, g}, rest} : Wr.Dec<Ht.Facts>}
      %Equal.sym(Wr.Dec<Hx.Cause>, SpT.r_cause(Wr.get_nat(SpW.w_cause(c, r1))), Wr.Got{c, r1}, ht.cause_rt(c, r1)) : {SpT.r_task.cause(_) == q : Wr.Dec<Ht.Facts>}
      %Equal.sym(Wr.Dec<Ht.Goal>, SpT.r_goal(Wr.get_nat(r1)), Wr.Got{g, rest}, ht.goal_rt(g, rest)) : {SpT.r_task.goal(c, _) == q : Wr.Dec<Ht.Facts>}
      {==}

# The reply
# ---------

# the entry spells a task's exit as the spec does
def ht.put(v: Ht.Verdict, -rest: String) -> {FHt.put_verdict(v, rest) == SpT.w_verdict(v, rest) : String}:
  match v:
    case Ht.Verdict{n, t}:
      match t:
        case Ht.Stands{}:
          {==}
        case Ht.Incomplete{}:
          {==}
