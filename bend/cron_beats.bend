# cron_beats: the records of the cron job store (`AgentCronJobStore`,
# crates/eukhe-core/src/cron/store/) as its actions change them: which
# records each action touches, with the per-job decisions of
# bend/cron_store.bend. The law cron_heartbeat_unique (laws/cron.bend)
# speaks of it: a session keeps at most one live `/heartbeat` job.
#
# A record carries the live session it runs in, its session file, whether
# it is the session's `/heartbeat` job (source `heartbeat`; a cron job, an
# agent-owned RLM heartbeat and a quota resume are not) and its facts. The
# order of the records does not matter to the law: a new one comes first
# here (the store appends it). A store action that changes several jobs one
# by one (`cancel_jobs_for_session`, a cancel by id) is a sequence of
# per-job actions.

import Base
import ./cron_store.bend as CS

# one record of the jobs file
type Row is Data:
  Row{sess: Nat, file: Nat, hb: Bool, f: CS.Fact}

# a per-job decision; `r` is the next match of a rule (Rust's arithmetic)
type Op is Data:
  OTake{claimed: Bool, due: Nat, now: Nat, r: Nat}
  ORecover{cleared: Bool}
  OFinish{u: Nat, ran: Bool, failed: Bool, now: Nat, r: Nat}
  OCancel{}
  OResume{now: Nat, r: Nat}
  OHalt{how: CS.Halt}
  OEdit{at: Maybe<&2, Nat>}

# a store action
type Act is Data:
  # `create_heartbeat` (heartbeat.rs): the session's heartbeats stop, a new
  # one runs on plan p first at `at`
  AHeartbeat{s: Nat, file: Nat, p: CS.Plan, at: Nat}
  # `create`, `create_rlm_heartbeat`: a job that is no `/heartbeat` job
  AJob{s: Nat, file: Nat, p: CS.Plan, at: Nat}
  # a per-job decision on the i-th record (none past the last)
  AOn{i: Nat, op: Op}
  # `rebind_session_jobs` (jobs.rs): every record of live session s or of
  # session file `file` moves to both; then every heartbeat of s but the
  # `keep`-th record (Rust keeps the newest) stops
  ARebind{s: Nat, file: Nat, keep: Nat}
  # a corrupt jobs file: an update moves it aside and starts from no records
  ALose{}

# Facts after a decision
# ----------------------

def next_at(n: CS.Next, +r: Nat) -> Maybe<&2, Nat>:
  match n:
    case CS.NNone{}:
      None{}
    case CS.NAt{ms}:
      Some{ms}
    case CS.NRoll{}:
      Some{r}

def took(t: CS.Took, +r: Nat, f: CS.Fact) -> CS.Fact:
  match t:
    case CS.Keep{}:
      f
    case CS.Roll{n}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st, p, next_at(n, r), k}
    case CS.Claimed{n}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st, p, next_at(n, r), k}

def back(b: CS.Back, f: CS.Fact) -> CS.Fact:
  match b:
    case CS.Kept{}:
      f
    case CS.Interrupted{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, nx2, k}

def fin(x: CS.Fin, +r: Nat, f: CS.Fact) -> CS.Fact:
  match x:
    case CS.Untouched{}:
      f
    case CS.Ran{st2, n, k2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, next_at(n, r), k2}
    case CS.Skipped{st2, n, k2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, next_at(n, r), k2}

def cut(x: CS.Cut, f: CS.Fact) -> CS.Fact:
  match x:
    case CS.Same{}:
      f
    case CS.Cut{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, nx2, k}

def again(x: CS.Again, +r: Nat, f: CS.Fact) -> CS.Fact:
  match x:
    case CS.Resumed{st2, n, k2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, next_at(n, r), k2}
    case CS.Ended{}:
      f
    case CS.NotRecurring{}:
      f

def edited(x: CS.Edit, f: CS.Fact) -> CS.Fact:
  match x:
    case CS.Locked{}:
      f
    case CS.Edited{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, nx2, k}

# the facts of a job after the decision op
def apply(op: Op, +f: CS.Fact) -> CS.Fact:
  match op:
    case OTake{c, d, n, r}:
      took(CS.take(f, c, d, n), r, f)
    case ORecover{c}:
      back(CS.recover(f, c), f)
    case OFinish{u, a, b, n, r}:
      fin(CS.finish(u, f, a, b, n), r, f)
    case OCancel{}:
      cut(CS.cancel(f), f)
    case OResume{n, r}:
      again(CS.resume(f, n), r, f)
    case OHalt{how}:
      cut(CS.halt(f, how), f)
    case OEdit{at}:
      edited(CS.edit(f, at), f)

# a new job on plan p, first at `at`
def made(m: CS.Made, p: CS.Plan) -> CS.Fact:
  match m:
    case CS.Made{st, n, k}:
      CS.Fact{st, p, Some{n}, k}

# The records
# -----------

# a stopped job: the user's stop (an active or paused job is cancelled)
def stopped(+f: CS.Fact) -> CS.Fact:
  cut(CS.halt(f, CS.HStop{}), f)

def stop_if(b: Bool, +f: CS.Fact) -> CS.Fact:
  match b:
    case True{}:
      stopped(f)
    case False{}:
      f

# a record of session s stops when it is a heartbeat
def stop_row(+s: Nat, r: Row) -> Row:
  match r:
    case Row{+s2, fl, +hb, f}:
      Row{s2, fl, hb, stop_if(Bool.and(Nat.is_eq(s2, s), hb), f)}

# every heartbeat of session s stops
def stop_beats(+s: Nat, rs: List<&2, Row>) -> List<&2, Row>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      stop_row(s, r) <> stop_beats(s, t)

# every heartbeat of session s but the k-th record stops
def stop_but(+s: Nat, k: Nat, rs: List<&2, Row>) -> List<&2, Row>:
  match k:
    case 0n:
      match rs:
        case Nil{}:
          Nil{}
        case r <> t:
          r <> stop_beats(s, t)
    case 1n+q:
      match rs:
        case Nil{}:
          Nil{}
        case r <> t:
          stop_row(s, r) <> stop_but(s, q, t)

def relabel.go(b: Bool, s: Nat, file: Nat, s2: Nat, fl: Nat, hb: Bool, f: CS.Fact) -> Row:
  match b:
    case True{}:
      Row{s, file, hb, f}
    case False{}:
      Row{s2, fl, hb, f}

# a record of live session s or of session file `file` moves to both
def relabel_row(+s: Nat, +file: Nat, r: Row) -> Row:
  match r:
    case Row{+s2, +fl, hb, f}:
      relabel.go(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), s, file, s2, fl, hb, f)

def relabel(+s: Nat, +file: Nat, rs: List<&2, Row>) -> List<&2, Row>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      relabel_row(s, file, r) <> relabel(s, file, t)

def on_row(op: Op, r: Row) -> Row:
  match r:
    case Row{s2, fl, hb, f}:
      Row{s2, fl, hb, apply(op, f)}

# the decision op on the i-th record
def on(i: Nat, +op: Op, rs: List<&2, Row>) -> List<&2, Row>:
  match i:
    case 0n:
      match rs:
        case Nil{}:
          Nil{}
        case r <> t:
          on_row(op, r) <> t
    case 1n+q:
      match rs:
        case Nil{}:
          Nil{}
        case r <> t:
          r <> on(q, op, t)

# the records after action a
def step(a: Act, rs: List<&2, Row>) -> List<&2, Row>:
  match a:
    case AHeartbeat{+s, file, p, at}:
      Row{s, file, True{}, made(CS.make(at), p)} <> stop_beats(s, rs)
    case AJob{s, file, p, at}:
      Row{s, file, False{}, made(CS.make(at), p)} <> rs
    case AOn{i, op}:
      on(i, op, rs)
    case ARebind{+s, file, keep}:
      stop_but(s, keep, relabel(s, file, rs))
    case ALose{}:
      Nil{}

# the records after the actions, from rs
def go(acts: List<&2, Act>, rs: List<&2, Row>) -> List<&2, Row>:
  match acts:
    case Nil{}:
      rs
    case a <> t:
      go(t, step(a, rs))

def run(acts: List<&2, Act>) -> List<&2, Row>:
  go(acts, Nil{})
