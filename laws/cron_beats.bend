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
# job, and of a job fired again (active, its next run `at`: the occurrence
# of its cleared claim record); a finish (jobs.rs
# `record_dispatch_result`) leaves an untouched job and writes the status,
# next run and failures in a row of a job that ran
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

def back_sets_spec(b: CS.Back, at: Nat) -> Sets:
  match b:
    case CS.Kept{}:
      SKeep{}
    case CS.Interrupted{st, nx}:
      SStNext{st, nx}
    case CS.Refire{}:
      SStNext{Cr.Active{}, Some{at}}

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
    case CB.ORecover{c, at}:
      back_sets_spec(CronStore.recover_spec(f, c), at)
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

# What every action writes on every record
# ----------------------------------------
# The store's whole answer to each action, record by record
# (crates/eukhe-core/src/cron/store/): a new heartbeat of session s
# (heartbeat.rs `create_heartbeat`) comes first, active on its plan with
# its first run and no failures, and the user's stop is applied to every
# `/heartbeat` record of session s and to no other record (another
# session's heartbeat, a job of another source); a new job of another
# source comes first unflagged and every record stays; a per-job decision
# is decide_spec; a rebind (jobs.rs `rebind_session_jobs`) moves every
# record of session s or of session file `file` to both, then stops every
# moved `/heartbeat` record but the `keep`-th record of the file (counted
# from 0; none kept past the last); a corrupt file leaves no record. The
# stop and the new job's facts are the spec's (laws/cron_store.bend
# `halt_spec`, `make_spec`).

# the facts of a new job on plan p, first at `at`
def made_spec(m: CS.Made, p: CS.Plan) -> CS.Fact:
  match m:
    case CS.Made{st, n, k}:
      CS.Fact{st, p, Some{n}, k}

# the record a new job writes: session s, session file `file`, the
# `/heartbeat` flag hb
def new_row_spec(s: Nat, file: Nat, hb: Bool, p: CS.Plan, at: Nat) -> CB.Row:
  CB.Row{s, file, hb, made_spec(CronStore.make_spec(at), p)}

# facts f after the user's stop (an active or paused job is cancelled with
# no next run; a finished or cancelled one stays)
def stopped_spec(+f: CS.Fact) -> CS.Fact:
  written_spec(cut_sets_spec(CronStore.halt_spec(f, CS.HStop{})), f)

# facts f, stopped when b holds
def stop_when_spec(b: Bool, +f: CS.Fact) -> CS.Fact:
  match b:
    case True{}:
      stopped_spec(f)
    case False{}:
      f

# a record after a new heartbeat of session s: stopped when it is a
# `/heartbeat` record of session s
def beat_row_spec(+s: Nat, r: CB.Row) -> CB.Row:
  match r:
    case CB.Row{+s2, fl, +hb, +f}:
      CB.Row{s2, fl, hb, stop_when_spec(Bool.and(hb, Nat.is_eq(s2, s)), f)}

def beat_rows_spec(+s: Nat, rs: List<&2, CB.Row>) -> List<&2, CB.Row>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      beat_row_spec(s, r) <> beat_rows_spec(s, t)

def moved_row_spec(moved: Bool, kept: Bool, +s: Nat, +file: Nat, s2: Nat, fl: Nat, +hb: Bool, +f: CS.Fact) -> CB.Row:
  match moved:
    case True{}:
      CB.Row{s, file, hb, stop_when_spec(Bool.and(hb, Bool.not(kept)), f)}
    case False{}:
      CB.Row{s2, fl, hb, f}

# the record at index i after a rebind of session s to session file
# `file` that keeps the `keep`-th record
def rebound_row_spec(+s: Nat, +file: Nat, +keep: Nat, +i: Nat, r: CB.Row) -> CB.Row:
  match r:
    case CB.Row{+s2, +fl, hb, f}:
      moved_row_spec(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), Nat.is_eq(i, keep), s, file, s2, fl, hb, f)

# the records rs, the first at index i, after that rebind
def rebound_spec(rs: List<&2, CB.Row>, +s: Nat, +file: Nat, +keep: Nat, +i: Nat) -> List<&2, CB.Row>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      rebound_row_spec(s, file, keep, i, r) <> rebound_spec(t, s, file, keep, 1n+i)

# the records after action a, from rs
def beats_step_spec(a: CB.Act, rs: List<&2, CB.Row>) -> List<&2, CB.Row>:
  match a:
    case CB.AHeartbeat{+s, file, p, at}:
      new_row_spec(s, file, True{}, p, at) <> beat_rows_spec(s, rs)
    case CB.AJob{s, file, p, at}:
      new_row_spec(s, file, False{}, p, at) <> rs
    case CB.AOn{i, op}:
      decide_spec(rs, i, op)
    case CB.ARebind{s, file, keep}:
      rebound_spec(rs, s, file, keep, 0n)
    case CB.ALose{}:
      Nil{}

# LAW cron_beats_step_exact: from any records, every store action writes exactly the spec's records: a new heartbeat of session s comes first (session s, its session file, flagged, active on its plan, first at `at`, no failures) and stops only the `/heartbeat` records of session s, every other record (another session's heartbeat, a job of another source) kept exactly; a new job of another source comes first unflagged and keeps every record; a per-job decision is cron_beats_decide_exact; a rebind of session s to session file `file` moves exactly the records of session s or of that file to both and stops exactly the moved `/heartbeat` records but the `keep`-th record, every other record kept exactly; a corrupt file leaves no record
# EXCLUDES: a new heartbeat that stops another session's heartbeat or a job of another source, or leaves a heartbeat of its session live; a rebind that moves, stops or keeps the wrong records; an action that reorders, drops or adds a record
law cron_beats_step_exact:
  for +a: CB.Act
  for +rs: List<&2, CB.Row>
  {CB.step(a, rs) == beats_step_spec(a, rs) : List<&2, CB.Row>}

# LAW cron_heartbeat_other_session_example: anchor: session 0 creates its heartbeat (every minute, first at 0), then session 1 creates its own (first at 5): both stay active, session 0's with its next run still at 0
# EXCLUDES: a new heartbeat of one session that stops another session's heartbeat
law cron_heartbeat_other_session_example:
  {CB.run([CB.AHeartbeat{0n, 0n, CS.PEvery{60000n}, 0n}, CB.AHeartbeat{1n, 1n, CS.PEvery{60000n}, 5n}]) == [CB.Row{1n, 1n, True{}, CS.Fact{Cr.Active{}, CS.PEvery{60000n}, Some{5n}, 0n}}, CB.Row{0n, 0n, True{}, CS.Fact{Cr.Active{}, CS.PEvery{60000n}, Some{0n}, 0n}}] : List<&2, CB.Row>}
