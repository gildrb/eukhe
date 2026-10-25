# eukhe: the laws of area cron_store

import Base
import ../bend/cron.bend as Cr
import ../bend/cron_store.bend as CS

# ---- cron_store ----

# LAWS (D2.2): the per-job decisions of the cron job store, the code the
# entry bend/ffi_cron.bend runs (bend/cron_store.bend). Each decision is
# exactly the spec below, on a clock of any unit u (the store's: ms, a
# minute being 60000). laws/cron.bend reads these specs for the entry's
# replies and ties each one to the model's step (`cron_*_refines`).
# PROOF.bend proves them (as CronStore.<law>) in proof/cron_store/.

# Terms
# -----

# the pause in minutes after the k-th failure in a row: 2 minutes,
# doubling, at most 60 (2, 2, 4, 8, 16, 32, then 60)
def pause_min_spec(k: Nat) -> Nat:
  match k:
    case 0n:
      2n
    case 1n:
      2n
    case 2n:
      4n
    case 3n:
      8n
    case 4n:
      16n
    case 5n:
      32n
    case 6n+r:
      60n

# the failures in a row at which a job stops
def cap_spec() -> Nat:
  8n

# the next run of a plan after now: a one-shot has none, an interval adds
# its length, a rule's next match is for Rust to compute
def next_spec(p: CS.Plan, +now: Nat) -> CS.Next:
  match p:
    case CS.POnce{}:
      CS.NNone{}
    case CS.PEvery{ms}:
      CS.NAt{Nat.add(now, ms)}
    case CS.PRule{}:
      CS.NRoll{}

def once_spec(p: CS.Plan) -> Bool:
  match p:
    case CS.POnce{}:
      True{}
    case CS.PEvery{ms}:
      False{}
    case CS.PRule{}:
      False{}

# a stored next run, as the entry answers it
def next_of_spec(m: Maybe<&2, Nat>) -> CS.Next:
  match m:
    case None{}:
      CS.NNone{}
    case Some{n}:
      CS.NAt{n}

def take_spec.due(le: Bool, claimed: Bool, p: CS.Plan, +now: Nat) -> CS.Took:
  match le:
    case False{}:
      CS.Keep{}
    case True{}:
      match claimed:
        case True{}:
          CS.Roll{next_spec(p, now)}
        case False{}:
          CS.Claimed{next_spec(p, now)}

# a claim pass: an active job whose next run is at or before `due` rolls
# its next run past `now`; it is claimed only when no claim of it is on
# record; every other job stays
def take_spec(f: CS.Fact, claimed: Bool, +due: Nat, +now: Nat) -> CS.Took:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              CS.Keep{}
            case Some{n}:
              take_spec.due(Nat.is_le(n, due), claimed, p, now)
        case Cr.Paused{}:
          CS.Keep{}
        case Cr.Finished{}:
          CS.Keep{}
        case Cr.Cancelled{}:
          CS.Keep{}

# a recovery clears this process's claim when this process no longer runs
# it, and another process's claim only when that process is dead
def clear_spec(w: CS.Who) -> Bool:
  match w:
    case CS.Mine{running}:
      match running:
        case True{}:
          False{}
        case False{}:
          True{}
    case CS.Theirs{dead}:
      dead

def recover_spec.on(st: Cr.Status, once: Bool, nx: Maybe<&2, Nat>) -> CS.Back:
  match st:
    case Cr.Active{}:
      match once:
        case True{}:
          CS.Interrupted{Cr.Finished{}, None{}}
        case False{}:
          CS.Interrupted{Cr.Active{}, nx}
    case Cr.Paused{}:
      CS.Kept{}
    case Cr.Finished{}:
      CS.Kept{}
    case Cr.Cancelled{}:
      CS.Kept{}

# a cleared claim interrupts an active job's run: a one-shot is finished
# with no next run, a repeating job keeps its next run; nothing else
# changes
def recover_spec(f: CS.Fact, cleared: Bool) -> CS.Back:
  match f:
    case CS.Fact{st, p, nx, k}:
      match cleared:
        case False{}:
          CS.Kept{}
        case True{}:
          recover_spec.on(st, once_spec(p), nx)

def later_spec.pick(b: Bool, n: Nat, w: Nat) -> Nat:
  match b:
    case True{}:
      w
    case False{}:
      n

# the next run after a failure: the stored next run, but never before the
# pause ends at w
def later_spec(nx: Maybe<&2, Nat>, +w: Nat) -> Nat:
  match nx:
    case None{}:
      w
    case Some{+n}:
      later_spec.pick(Nat.is_lt(n, w), n, w)

def finish_spec.fail(under: Bool, nx: Maybe<&2, Nat>, +k: Nat, +now: Nat, +u: Nat) -> CS.Fin:
  match under:
    case True{}:
      CS.Ran{Cr.Active{}, CS.NAt{later_spec(nx, Nat.add(now, Nat.mul(pause_min_spec(k), u)))}, k}
    case False{}:
      CS.Ran{Cr.Paused{}, CS.NNone{}, k}

def finish_spec.on(failed: Bool, ran: Bool, once: Bool, p: CS.Plan, nx: Maybe<&2, Nat>, +k: Nat, +now: Nat, +u: Nat) -> CS.Fin:
  match failed:
    case True{}:
      match once:
        case True{}:
          CS.Ran{Cr.Finished{}, CS.NNone{}, 1n+k}
        case False{}:
          finish_spec.fail(Nat.is_lt(1n+k, cap_spec()), nx, 1n+k, now, u)
    case False{}:
      match ran:
        case True{}:
          match once:
            case True{}:
              CS.Ran{Cr.Finished{}, CS.NNone{}, 0n}
            case False{}:
              CS.Ran{Cr.Active{}, next_of_spec(nx), 0n}
        case False{}:
          match once:
            case True{}:
              CS.Skipped{Cr.Finished{}, CS.NNone{}, k}
            case False{}:
              CS.Skipped{Cr.Active{}, next_spec(p, now), k}

# the finish step of an active job's run (on clock unit u): a failure
# (ran or skipped) counts one more in a row, and the job then pauses at the
# cap, or else runs again after the pause (never before its next run); a
# good run sets the count to 0 and keeps the next run; a skip keeps the
# count and rolls the next run past now; a one-shot is finished with no
# next run either way. A job that is not active is untouched
def finish_spec(+u: Nat, f: CS.Fact, ran: Bool, failed: Bool, +now: Nat) -> CS.Fin:
  match f:
    case CS.Fact{st, +p, nx, k}:
      match st:
        case Cr.Active{}:
          finish_spec.on(failed, ran, once_spec(p), p, nx, k, now, u)
        case Cr.Paused{}:
          CS.Untouched{}
        case Cr.Finished{}:
          CS.Untouched{}
        case Cr.Cancelled{}:
          CS.Untouched{}

# a job that is not cancelled is cancelled, with no next run
def cancel_spec(f: CS.Fact) -> CS.Cut:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Cancelled{}:
          CS.Same{}
        case Cr.Active{}:
          CS.Cut{Cr.Cancelled{}, None{}}
        case Cr.Paused{}:
          CS.Cut{Cr.Cancelled{}, None{}}
        case Cr.Finished{}:
          CS.Cut{Cr.Cancelled{}, None{}}

def resume_spec.plan(p: CS.Plan, +now: Nat) -> CS.Again:
  match p:
    case CS.POnce{}:
      CS.NotRecurring{}
    case CS.PEvery{ms}:
      CS.Resumed{Cr.Active{}, CS.NAt{Nat.add(now, ms)}, 0n}
    case CS.PRule{}:
      CS.Resumed{Cr.Active{}, CS.NRoll{}, 0n}

# an active or paused repeating job is active again, its next run its
# schedule's after now, its failures in a row 0; a finished or cancelled
# job has nothing to resume; a one-shot is not recurring
def resume_spec(f: CS.Fact, +now: Nat) -> CS.Again:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          resume_spec.plan(p, now)
        case Cr.Paused{}:
          resume_spec.plan(p, now)
        case Cr.Finished{}:
          CS.Ended{}
        case Cr.Cancelled{}:
          CS.Ended{}

# Laws
# ----

# LAW cron_take_exact: a claim pass of the model that runs is the spec's on every fact, claim on record, due time and clock
law cron_take_exact:
  for +f: CS.Fact
  for +c: Bool
  for +d: Nat
  for +n: Nat
  {CS.take(f, c, d, n) == take_spec(f, c, d, n) : CS.Took}

# LAW cron_clear_exact: the verdict of the model that runs on a claim on record is the spec's: this process's claim clears exactly when it no longer runs it, another's exactly when that process is dead
law cron_clear_exact:
  for +w: CS.Who
  {CS.clear(w) == clear_spec(w) : Bool}

# LAW cron_recover_exact: a recovery of the model that runs is the spec's on every fact, cleared or not
law cron_recover_exact:
  for +f: CS.Fact
  for +c: Bool
  {CS.recover(f, c) == recover_spec(f, c) : CS.Back}

# LAW cron_finish_exact: the finish step of the model that runs is the spec's on a clock of every unit u (the pause u times the spec's minutes), every fact, result and clock
law cron_finish_exact:
  for +u: Nat
  for +f: CS.Fact
  for +r: Bool
  for +b: Bool
  for +n: Nat
  {CS.finish(u, f, r, b, n) == finish_spec(u, f, r, b, n) : CS.Fin}

# LAW cron_cancel_exact: a cancel of the model that runs is the spec's on every fact
law cron_cancel_exact:
  for +f: CS.Fact
  {CS.cancel(f) == cancel_spec(f) : CS.Cut}

# LAW cron_resume_exact: a resume of the model that runs is the spec's on every fact and clock
law cron_resume_exact:
  for +f: CS.Fact
  for +n: Nat
  {CS.resume(f, n) == resume_spec(f, n) : CS.Again}
