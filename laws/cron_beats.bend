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

import Base
import ../bend/cron.bend as Cr
import ../bend/cron_store.bend as CS
import ../bend/cron_beats.bend as CB
import ./cron.bend as Cron

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
