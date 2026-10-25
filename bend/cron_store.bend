# cron_store: the per-job decisions of the cron job store
# (`AgentCronJobStore`, crates/eukhe-core/src/cron/store/), the code the
# entry bend/ffi_cron.bend runs. The store's clock counts milliseconds;
# the model of the shared file (bend/cron.bend) counts minutes: each
# decision here takes the clock unit `u` (MINUTE in the shipped entry), and
# the laws (laws/cron.bend, the `cron_*_refines` laws) tie each one to the
# model's `take`, `recover`, `finish`, `cancel` and `resume` on every unit.
#
# Rust reads the jobs file and gathers the facts of one job (its status,
# its schedule, its next run, its failures in a row, whether a claim of it
# is on record or was cleared, the clock); each decision answers what the
# job becomes. Rust keeps the file, its lock, the claim records, the ids,
# the liveness probe and the set of the runs of this process.

import Base
import ./cron.bend as Cr

# Facts
# -----

# a schedule as the store keeps it: a one-shot, an interval of ms (more
# than 0), or a rule Rust evaluates (a cron expression)
type Plan is Data:
  POnce{}
  PEvery{ms: Nat}
  PRule{}

# the store's record of a job: its status, schedule, next run (ms) and
# failures in a row
type Fact is Data:
  Fact{st: Cr.Status, plan: Plan, next: Maybe<&2, Nat>, streak: Nat}

# a next run: none, at a time (ms), or the rule's next match after the
# decision's clock (Rust evaluates the rule)
type Next is Data:
  NNone{}
  NAt{ms: Nat}
  NRoll{}

# whose claim is on record: this process's (and whether this process still
# runs it), or another process's (and whether that process is dead)
type Who is Data:
  Mine{running: Bool}
  Theirs{dead: Bool}

# what Rust asks about one job
type Ask is Data:
  AskTake{f: Fact, claimed: Bool, due: Nat, now: Nat}
  AskClear{w: Who}
  AskRecover{f: Fact, cleared: Bool}
  AskFinish{f: Fact, ran: Bool, failed: Bool, now: Nat}
  AskCancel{f: Fact}
  AskResume{f: Fact, now: Nat}

# Answers
# -------

# a claim pass: not due; due with a claim on record (roll its next run);
# due with none (claim it and roll its next run)
type Took is Data:
  Keep{}
  Roll{n: Next}
  Claimed{n: Next}

# a recovery: nothing changes, or the job records the interruption of its
# run with this status and next run
type Back is Data:
  Kept{}
  Interrupted{st: Cr.Status, next: Maybe<&2, Nat>}

# a finish step: the job is not active (only its claim goes), it counts a
# run, or it counts a skip
type Fin is Data:
  Untouched{}
  Ran{st: Cr.Status, n: Next, k: Nat}
  Skipped{st: Cr.Status, n: Next, k: Nat}

# a cancel: already cancelled, or this status and next run
type Cut is Data:
  Same{}
  Cut{st: Cr.Status, next: Maybe<&2, Nat>}

# a resume: this status, next run and failures in a row; a finished or
# cancelled job (nothing to resume); a one-shot (not recurring)
type Again is Data:
  Resumed{st: Cr.Status, n: Next, k: Nat}
  Ended{}
  NotRecurring{}

# The clock
# ---------

# the store's clock unit: a minute in ms
def MINUTE() -> Nat:
  60000n

# the pause after the k-th failure in a row, in units u (Cr.delay minutes)
def pause(k: Nat, +u: Nat) -> Nat:
  Nat.mul(Cr.delay(k), u)

# Small parts
# -----------

def as_next(m: Maybe<&2, Nat>) -> Next:
  match m:
    case None{}:
      NNone{}
    case Some{n}:
      NAt{n}

# the next run of a plan after now
def roll(p: Plan, +now: Nat) -> Next:
  match p:
    case POnce{}:
      NNone{}
    case PEvery{ms}:
      NAt{Nat.add(now, ms)}
    case PRule{}:
      NRoll{}

def plan_once(p: Plan) -> Bool:
  match p:
    case POnce{}:
      True{}
    case PEvery{ms}:
      False{}
    case PRule{}:
      False{}

# A claim pass
# ------------

def take.due(due: Bool, claimed: Bool, p: Plan, +now: Nat) -> Took:
  match due:
    case False{}:
      Keep{}
    case True{}:
      match claimed:
        case True{}:
          Roll{roll(p, now)}
        case False{}:
          Claimed{roll(p, now)}

def take.next(nx: Maybe<&2, Nat>, +due: Nat, claimed: Bool, p: Plan, +now: Nat) -> Took:
  match nx:
    case None{}:
      Keep{}
    case Some{n}:
      take.due(Nat.is_le(n, due), claimed, p, now)

# an active job whose next run is at or before due rolls its next run
# after now; it is claimed when no claim of it is on record (Cr.take)
def take(f: Fact, claimed: Bool, +due: Nat, +now: Nat) -> Took:
  match f:
    case Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          take.next(nx, due, claimed, p, now)
        case Cr.Paused{}:
          Keep{}
        case Cr.Finished{}:
          Keep{}
        case Cr.Cancelled{}:
          Keep{}

# A recovery
# ----------

# a recovery clears this process's claim with no run of it here, or the
# claim of a dead process (Cr.clears)
def clear(w: Who) -> Bool:
  match w:
    case Mine{running}:
      Bool.not(running)
    case Theirs{dead}:
      dead

def recover.go(st: Cr.Status, once: Bool, nx: Maybe<&2, Nat>) -> Back:
  match st:
    case Cr.Active{}:
      match once:
        case True{}:
          Interrupted{Cr.Finished{}, None{}}
        case False{}:
          Interrupted{Cr.Active{}, nx}
    case Cr.Paused{}:
      Kept{}
    case Cr.Finished{}:
      Kept{}
    case Cr.Cancelled{}:
      Kept{}

# a cleared claim of an active job ends its run: an active one-shot is
# finished (Cr.recover)
def recover(f: Fact, cleared: Bool) -> Back:
  match f:
    case Fact{st, p, nx, k}:
      match cleared:
        case False{}:
          Kept{}
        case True{}:
          recover.go(st, plan_once(p), nx)

# The finish step
# ---------------

# a run's result: a failure counts whether it ran or was skipped
def outcome(failed: Bool, ran: Bool) -> Cr.Out:
  match failed:
    case True{}:
      Cr.Loss{}
    case False{}:
      match ran:
        case True{}:
          Cr.Win{}
        case False{}:
          Cr.Skip{}

def finish.fail(under: Bool, +now: Nat, nx: Maybe<&2, Nat>, +k: Nat, +u: Nat) -> Fin:
  match under:
    case True{}:
      Ran{Cr.Active{}, NAt{Cr.later(nx, Nat.add(now, pause(k, u)))}, k}
    case False{}:
      Ran{Cr.Paused{}, NNone{}, k}

def finish.win(once: Bool, nx: Maybe<&2, Nat>) -> Fin:
  match once:
    case True{}:
      Ran{Cr.Finished{}, NNone{}, 0n}
    case False{}:
      Ran{Cr.Active{}, as_next(nx), 0n}

def finish.loss(once: Bool, +now: Nat, nx: Maybe<&2, Nat>, +k: Nat, +u: Nat) -> Fin:
  match once:
    case True{}:
      Ran{Cr.Finished{}, NNone{}, 1n+k}
    case False{}:
      finish.fail(Nat.is_lt(1n+k, Cr.CAP()), now, nx, 1n+k, u)

def finish.skip(once: Bool, p: Plan, +k: Nat, +now: Nat) -> Fin:
  match once:
    case True{}:
      Skipped{Cr.Finished{}, NNone{}, k}
    case False{}:
      Skipped{Cr.Active{}, roll(p, now), k}

def finish.active(o: Cr.Out, +p: Plan, nx: Maybe<&2, Nat>, +k: Nat, +now: Nat, +u: Nat) -> Fin:
  match o:
    case Cr.Win{}:
      finish.win(plan_once(p), nx)
    case Cr.Loss{}:
      finish.loss(plan_once(p), now, nx, k, u)
    case Cr.Skip{}:
      finish.skip(plan_once(p), p, k, now)

# the result of the run of an active job: a good run sets the failures in
# a row to 0; a failure counts one more, backs off (never before the next
# run) or stops the job at the cap; a skip rolls the next run; a one-shot
# is finished (Cr.finish)
def finish(+u: Nat, f: Fact, ran: Bool, failed: Bool, +now: Nat) -> Fin:
  match f:
    case Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          finish.active(outcome(failed, ran), p, nx, k, now, u)
        case Cr.Paused{}:
          Untouched{}
        case Cr.Finished{}:
          Untouched{}
        case Cr.Cancelled{}:
          Untouched{}

# User actions
# ------------

# a job that is not cancelled is cancelled, with no next run (Cr.cancel)
def cancel(f: Fact) -> Cut:
  match f:
    case Fact{st, p, nx, k}:
      match st:
        case Cr.Cancelled{}:
          Same{}
        case Cr.Active{}:
          Cut{Cr.Cancelled{}, None{}}
        case Cr.Paused{}:
          Cut{Cr.Cancelled{}, None{}}
        case Cr.Finished{}:
          Cut{Cr.Cancelled{}, None{}}

def resume.plan(p: Plan, +now: Nat) -> Again:
  match p:
    case POnce{}:
      NotRecurring{}
    case PEvery{ms}:
      Resumed{Cr.Active{}, NAt{Nat.add(now, ms)}, 0n}
    case PRule{}:
      Resumed{Cr.Active{}, NRoll{}, 0n}

# an active or paused repeating job runs again on its schedule after now,
# its failures in a row forgotten (Cr.resume)
def resume(f: Fact, +now: Nat) -> Again:
  match f:
    case Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          resume.plan(p, now)
        case Cr.Paused{}:
          resume.plan(p, now)
        case Cr.Finished{}:
          Ended{}
        case Cr.Cancelled{}:
          Ended{}
