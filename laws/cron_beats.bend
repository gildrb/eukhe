# eukhe: the laws of area cron_beats (which records are `/heartbeat` jobs)
#
# The store's actions on its records (bend/cron_beats.bend): a new
# heartbeat (heartbeat.rs `create_heartbeat`), a new job of another source
# (`create`, `create_rlm_heartbeat`), a per-job decision on any record, a
# rebind of a live session to a session file (jobs.rs
# `rebind_session_jobs`), a corrupt file. A record carries a flag: it is
# its session's `/heartbeat` job (source `heartbeat`). laws/cron.bend
# (cron_heartbeat_unique) counts a session's live heartbeats by that flag;
# the laws here tie the flag to the action that wrote the record, so a
# heartbeat `create_heartbeat` makes is counted: only a new heartbeat
# writes a flagged record, no action sets or clears the flag of a record it
# keeps, and a new heartbeat is the one live `/heartbeat` job of its
# session, the one `heartbeat_get` (heartbeat.rs `get_heartbeat`) reads.
# A per-job decision on the i-th record writes on it exactly what the
# decision's answer names, the way the store applies each answer.

import Base
import ../bend/cron.bend as Cr
import ../bend/cron_store.bend as CS
import ../bend/cron_beats.bend as CB
import ./cron.bend as Cron
import ./cron_store.bend as CronStore

# Terms
# -----

# the `/heartbeat` flag of a record
def flag_spec(r: CB.Row) -> Bool:
  match r:
    case CB.Row{s, fl, hb, f}:
      hb

# the flags of the records, in order
def flags_spec(rs: List<&2, CB.Row>) -> List<&2, Bool>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      flag_spec(r) <> flags_spec(t)

# the flags of the records after action a, from flags fs: a new heartbeat
# adds one flagged record first, a new job of another source one unflagged
# record; a per-job decision and a rebind keep every record with its flag;
# a corrupt file leaves no record
def flags_after_spec(a: CB.Act, fs: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case CB.AHeartbeat{s, file, p, at}:
      True{} <> fs
    case CB.AJob{s, file, p, at}:
      False{} <> fs
    case CB.AOn{i, op}:
      fs
    case CB.ARebind{s, file, keep}:
      fs
    case CB.ALose{}:
      Nil{}

# r before rest when b holds, else rest
def keep_spec(b: Bool, r: CB.Row, rest: List<&2, CB.Row>) -> List<&2, CB.Row>:
  match b:
    case True{}:
      r <> rest
    case False{}:
      rest

# the live heartbeats of session s in rs, in order (active or paused
# `/heartbeat` jobs of s: what `heartbeat_get` reads from)
def beats_spec(+s: Nat, rs: List<&2, CB.Row>) -> List<&2, CB.Row>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> t:
      keep_spec(Cron.beat_spec(s, r), r, beats_spec(s, t))

# Laws
# ----

# LAW cron_heartbeat_flags: from any records, every store action keeps each record with its `/heartbeat` flag (a per-job decision and a rebind neither set nor clear one, and drop no record), and adds only a record flagged as a heartbeat for a new heartbeat and an unflagged one for a new job of another source; a corrupt file leaves no record
law cron_heartbeat_flags:
  for +a: CB.Act
  for +rs: List<&2, CB.Row>
  {flags_spec(CB.step(a, rs)) == flags_after_spec(a, flags_spec(rs)) : List<&2, Bool>}

# LAW cron_heartbeat_replaces: from any records, after a new heartbeat of session s on plan p, first at `at`, the live `/heartbeat` jobs of s are exactly one: the new one, of session s and session file `file`, active on plan p with its first run at `at` and no failures; every earlier heartbeat of s is stopped
law cron_heartbeat_replaces:
  for +s: Nat
  for +file: Nat
  for +p: CS.Plan
  for +at: Nat
  for +rs: List<&2, CB.Row>
  {beats_spec(s, CB.step(CB.AHeartbeat{s, file, p, at}, rs)) == [CB.Row{s, file, True{}, CS.Fact{Cr.Active{}, p, Some{at}, 0n}}] : List<&2, CB.Row>}

# LAW cron_heartbeat_replaces_example: session 0 creates its heartbeat twice (every minute, first at 0 then at 5): the records are the second heartbeat, active, and the first one, cancelled with no next run
law cron_heartbeat_replaces_example:
  {CB.run([CB.AHeartbeat{0n, 0n, CS.PEvery{60000n}, 0n}, CB.AHeartbeat{0n, 0n, CS.PEvery{60000n}, 5n}]) == [CB.Row{0n, 0n, True{}, CS.Fact{Cr.Active{}, CS.PEvery{60000n}, Some{5n}, 0n}}, CB.Row{0n, 0n, True{}, CS.Fact{Cr.Cancelled{}, CS.PEvery{60000n}, None{}, 0n}}] : List<&2, CB.Row>}

# What a per-job decision writes on a record
# ------------------------------------------
# The store applies each answer of bend/ffi_cron.bend and
# bend/ffi_cron_file.bend to the job's record this way
# (crates/eukhe-core/src/cron/store/): a claim pass (state.rs) leaves a
# job it keeps and writes only the next run of a job it rolls or claims; a
# recovery (state.rs) writes the status and next run of an interrupted
# job; a finish (jobs.rs `record_dispatch_result`) leaves an untouched job
# and writes the status, next run and failures in a row of a job that ran
# or skipped; a cancel, pause, stop or delete (jobs.rs, heartbeat.rs,
# rlm_heartbeat.rs) leaves a job already done and writes the status and
# next run of a cut one; a resume writes the status, next run and failures
# in a row, and leaves an ended or one-shot job; an edit (rlm_heartbeat.rs)
# leaves a locked job and writes the status and next run of an edited one.
# A next run the answer names is none, a time, or (a roll) the schedule's
# next match after the decision's clock, which Rust computes (facts.rs
# `next_text`): `r` here. The record keeps its session, its session file,
# its `/heartbeat` flag and its plan (an edit's new schedule is written by
# Rust beside the decision; it is not pinned here).

# the facts an answer writes: none, the next run, the status and next run,
# or the status, next run and failures in a row
type Sets is Data:
  SKeep{}
  SNext{nx: Maybe<&2, Nat>}
  SStNext{st: Cr.Status, nx: Maybe<&2, Nat>}
  SAll{st: Cr.Status, nx: Maybe<&2, Nat>, k: Nat}

# a next run an answer names; `r` is the schedule's next match
def next_run_spec(n: CS.Next, r: Nat) -> Maybe<&2, Nat>:
  match n:
    case CS.NNone{}:
      None{}
    case CS.NAt{ms}:
      Some{ms}
    case CS.NRoll{}:
      Some{r}

def took_sets_spec(t: CS.Took, r: Nat) -> Sets:
  match t:
    case CS.Keep{}:
      SKeep{}
    case CS.Roll{n}:
      SNext{next_run_spec(n, r)}
    case CS.Claimed{n}:
      SNext{next_run_spec(n, r)}

def back_sets_spec(b: CS.Back) -> Sets:
  match b:
    case CS.Kept{}:
      SKeep{}
    case CS.Interrupted{st, nx}:
      SStNext{st, nx}

def fin_sets_spec(x: CS.Fin, r: Nat) -> Sets:
  match x:
    case CS.Untouched{}:
      SKeep{}
    case CS.Ran{st, n, k}:
      SAll{st, next_run_spec(n, r), k}
    case CS.Skipped{st, n, k}:
      SAll{st, next_run_spec(n, r), k}

def cut_sets_spec(x: CS.Cut) -> Sets:
  match x:
    case CS.Same{}:
      SKeep{}
    case CS.Cut{st, nx}:
      SStNext{st, nx}

def again_sets_spec(x: CS.Again, r: Nat) -> Sets:
  match x:
    case CS.Resumed{st, n, k}:
      SAll{st, next_run_spec(n, r), k}
    case CS.Ended{}:
      SKeep{}
    case CS.NotRecurring{}:
      SKeep{}

def edit_sets_spec(x: CS.Edit) -> Sets:
  match x:
    case CS.Locked{}:
      SKeep{}
    case CS.Edited{st, nx}:
      SStNext{st, nx}

# what decision op on a job of facts f writes: the answer of the decision's
# spec (laws/cron_store.bend)
def sets_spec(op: CB.Op, +f: CS.Fact) -> Sets:
  match op:
    case CB.OTake{c, d, n, r}:
      took_sets_spec(CronStore.take_spec(f, c, d, n), r)
    case CB.ORecover{c}:
      back_sets_spec(CronStore.recover_spec(f, c))
    case CB.OFinish{u, a, b, n, r}:
      fin_sets_spec(CronStore.finish_spec(u, f, a, b, n), r)
    case CB.OCancel{}:
      cut_sets_spec(CronStore.cancel_spec(f))
    case CB.OResume{n, r}:
      again_sets_spec(CronStore.resume_spec(f, n), r)
    case CB.OHalt{how}:
      cut_sets_spec(CronStore.halt_spec(f, how))
    case CB.OEdit{at}:
      edit_sets_spec(CronStore.edit_spec(f, at))

# facts f with what w writes
def written_spec(w: Sets, f: CS.Fact) -> CS.Fact:
  match w:
    case SKeep{}:
      f
    case SNext{nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st, p, nx2, k}
    case SStNext{st2, nx2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, nx2, k}
    case SAll{st2, nx2, k2}:
      match f:
        case CS.Fact{st, p, nx, k}:
          CS.Fact{st2, p, nx2, k2}

# a record after decision op: it keeps its session, file and flag and takes
# what the decision writes
def decided_spec(+op: CB.Op, r: CB.Row) -> CB.Row:
  match r:
    case CB.Row{s, fl, hb, +f}:
      CB.Row{s, fl, hb, written_spec(sets_spec(op, f), f)}

# the records after decision op on the i-th of rs: that record is decided,
# every other record stays; past the last record nothing changes
def decide_spec(rs: List<&2, CB.Row>, i: Nat, +op: CB.Op) -> List<&2, CB.Row>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match i:
        case 0n:
          decided_spec(op, r) <> t
        case 1n+q:
          r <> decide_spec(t, q, op)

# LAW cron_beats_decide_exact: from any records, a per-job decision op on the i-th record changes only that record (none past the last): it keeps its session, session file, `/heartbeat` flag and plan, and takes the status, next run and failures in a row the decision's answer names (laws/cron_store.bend), as the store applies them
law cron_beats_decide_exact:
  for +i: Nat
  for +op: CB.Op
  for +rs: List<&2, CB.Row>
  {CB.step(CB.AOn{i, op}, rs) == decide_spec(rs, i, op) : List<&2, CB.Row>}
