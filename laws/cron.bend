# LAWS (D2): the cron store shared by processes. Each law is an open claim
# about the model in bend/cron.bend; PROOF.bend proves them (as
# Cronl.<law>) with the lemmas of bend/proof_cron.bend.

import Base
import ../bend/cron.bend as Cr

# (D2) Cron
# ---------
# docs/state.md D2. The cron jobs file `cron-jobs.json` (bend/cron.bend),
# shared by any number of processes. Every input is free: any events of
# any processes in any order (make a job, claim the due jobs, recover
# claims, finish a run good, failed or skipped, unwind a pass, die), any
# user actions (cancel, resume), any time, any records this build cannot
# read, a corrupt file at any point.

# LAW: after any events, each job is run by at most one process, and that
# run holds the claim on record; no occurrence of a job starts twice (the
# occurrences that started fall strictly, the newest first); a one-shot
# starts at most once
law cron_fires_once:
  for +evs: List<&2, Cr.Ev>
  Cr.FiresAll(Cr.S.recs(Cr.run(evs)))

# LAW: after any events, a finished one-shot has no run: it is finished
# only after its run ended
law cron_once_finished_after_end:
  for +evs: List<&2, Cr.Ev>
  Cr.EndsAll(Cr.S.recs(Cr.run(evs)))

# LAW: from any file (records read or not, corrupt or not), a step that
# is not the file's corruption keeps every record: each job record this
# build cannot read with the same bytes, each job, each claim record this
# build cannot read, the corrupt file (in place or moved aside, never
# written over), each file moved aside
law cron_never_drops:
  for +s: Cr.S
  for +e: Cr.Ev
  for +t: Nat
  for +i: Nat
  {Cr.Ev.is_corrupt(e) == False{} : Bool} -> Cr.Keeps(t, i, s, Cr.step(s, e))

# LAW: from any state, a step of process p removes the claim of process o
# on job i only when o is p or o is dead; no other step (but the file's
# corruption) removes a claim
law cron_claim_owned:
  for +s: Cr.S
  for +e: Cr.Ev
  for +i: Nat
  for +x: Nat
  for +o: Nat
  {Cr.Ev.is_corrupt(e) == False{} : Bool} -> {Cr.claim_of(i, Cr.S.recs(s)) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>} -> Or({Cr.claim_of(i, Cr.S.recs(Cr.step(s, e))) == Some{Cr.Claim{x, o}} : Maybe<&2, Cr.Claim>}, Or({Cr.Ev.by(e) == Some{o} : Maybe<&2, Nat>}, {Cr.has(o, Cr.S.dead(s)) == True{} : Bool}))

# LAW: after any events, a job counted at most CAP failed runs in a row,
# and an active job fewer: so the CAP-th failure in a row stops it; a
# stopped (paused) job stays stopped through every step that is not a user
# action; the pause after the k-th failure is never shorter than after the
# (k-1)-th, and a failure never moves the next run before its pause ends
law cron_backoff_bounded:
  for +evs: List<&2, Cr.Ev>
  for +s: Cr.S
  for +e: Cr.Ev
  for +i: Nat
  for +k: Nat
  for +c: Nat
  for +nx: Maybe<&2, Nat>
  (Cr.StopsAll(Cr.S.recs(Cr.run(evs))) & (({Cr.Ev.is_user(e) == False{} : Bool} -> Cr.StaysPaused(i, s, Cr.step(s, e))) & ({Nat.is_le(Cr.delay(k), Cr.delay(1n+k)) == True{} : Bool} & {Nat.is_le(Nat.add(c, Cr.delay(k)), Cr.later(nx, Nat.add(c, Cr.delay(k)))) == True{} : Bool})))
