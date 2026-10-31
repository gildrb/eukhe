# eukhe: the laws of area cron (the user's actions on one job)
#
# The cron store changes a job's status from outside a run only through
# the entry bend/ffi_cron.bend: a pause, a stop (the cancels of a
# session's jobs, of a heartbeat replaced by a new one, of a cleared
# heartbeat), a delete, an edit of the schedule, a new job
# (crates/eukhe-core/src/cron/store/jobs.rs, heartbeat.rs,
# rlm_heartbeat.rs). laws/cron.bend (cron_entry_answers) pins the entry to
# the specs of laws/cron_store.bend; each law here ties a spec, applied to
# a model job on a clock of any unit u (the store's: a minute is 60000
# ms), to the model's step of bend/cron.bend, whose laws (cron_fires_once,
# cron_never_drops, cron_claim_owned, cron_backoff_bounded) cover these
# events too.

import Base
import ../bend/cron.bend as Cr
import ../bend/cron_store.bend as CS
import ../bend/ffi_cron.bend as FC
import ./cron.bend as Cron
import ./cron_store.bend as CronStore

# Terms
# -----

# an edit, applied: a locked job stays; an edited one takes this status and
# next run, its failures in a row and claim kept
def edit_view(x: CS.Edit, j: Cr.Job, +u: Nat) -> Cron.View():
  match x:
    case CS.Locked{}:
      Cron.view(j, u)
    case CS.Edited{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          (st2, (CronStore.next_of_spec(m), (k, Cron.scale_claim(cl, u))))

# a job as the laws compare it: its status, next run, failures in a row and
# claim on record
type JV is Data:
  JV{st: Cr.Status, n: CS.Next, k: Nat, cl: Maybe<&2, Cr.Claim>}

# a new job, as Rust writes it: no claim on record
def made_jv(x: CS.Made) -> JV:
  match x:
    case CS.Made{st, n, k}:
      JV{st, CS.NAt{n}, k, None{}}

def last_job.pick(m: Maybe<&2, Cr.Job>, j: Cr.Job) -> Maybe<&2, Cr.Job>:
  match m:
    case None{}:
      Some{j}
    case Some{x}:
      Some{x}

# the last job record of rs
def last_job(rs: List<&2, Cr.Rec>) -> Maybe<&2, Cr.Job>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      match r:
        case Cr.Raw{x}:
          last_job(t)
        case Cr.Known{j}:
          last_job.pick(last_job(t), j)

def last_jv(m: Maybe<&2, Cr.Job>, +u: Nat) -> Maybe<&2, JV>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          Some{JV{st, CronStore.next_of_spec(Cron.scale_opt(nx, u)), k, Cron.scale_claim(cl, u)}}

def clock_of(s: Cr.S) -> Nat:
  match s:
    case Cr.S{b, rs, rd, dead, c, n, a}:
      c

# Laws
# ----

# LAW cron_pause_refines: on a clock of any unit u, a pause applied to a model job is the model's pause (Cr.pause): the same status, next run, failures in a row and claim on record
# EXCLUDES: a pause that leaves a next run (the job would fire while paused), that pauses a finished or
#   cancelled job, that drops a claim or resets the failures in a row
law cron_pause_refines:
  for +v: Nat
  for +j: Cr.Job
  {Cron.cut_view(CronStore.halt_spec(Cron.fact_of(j, 1n+v), CS.HPause{}), j, 1n+v) == Cron.view(Cr.pause(j), 1n+v) : Cron.View()}

# LAW cron_stop_refines: on a clock of any unit u, a stop (a session's or a heartbeat's cancel) applied to a model job is the model's stop (Cr.stop)
# EXCLUDES: a stop that cancels a finished job (the entry's cancel does), that leaves a next run, or
#   that drops a claim
law cron_stop_refines:
  for +v: Nat
  for +j: Cr.Job
  {Cron.cut_view(CronStore.halt_spec(Cron.fact_of(j, 1n+v), CS.HStop{}), j, 1n+v) == Cron.view(Cr.stop(j), 1n+v) : Cron.View()}

# LAW cron_delete_refines: on a clock of any unit u, a delete applied to a model job is the model's delete (Cr.delete): cancelled with no next run, whatever its status
# EXCLUDES: a delete that skips a finished or cancelled job, that leaves a next run, or that drops a claim
law cron_delete_refines:
  for +v: Nat
  for +j: Cr.Job
  {Cron.cut_view(CronStore.halt_spec(Cron.fact_of(j, 1n+v), CS.HDelete{}), j, 1n+v) == Cron.view(Cr.delete(j), 1n+v) : Cron.View()}

# LAW cron_edit_refines: on a clock of any unit u, an edit to the schedule Every{k} at the clock (its first run 1+k minutes later, as Rust computes it), applied to a model job, is the model's edit (Cr.edit)
# EXCLUDES: an edit that wakes a paused job (gives it a next run), that edits a finished or cancelled
#   job, that keeps the old next run of an active job, or that changes a status or a claim
law cron_edit_refines:
  for +v: Nat
  for +c: Nat
  for +k: Nat
  for +j: Cr.Job
  {edit_view(CronStore.edit_spec(Cron.fact_of(j, 1n+v), Some{Nat.mul(Nat.add(c, 1n+k), 1n+v)}), j, 1n+v) == Cron.view(Cr.edit(c, k, j), 1n+v) : Cron.View()}

# LAW cron_make_refines: on a clock of any unit u, the new job of a live process (its first run as Rust computes it from the schedule) is the job the model's step makes, the last record of the file: active, that first run, no failures in a row, no claim
# EXCLUDES: a new job made paused, with a failure count, a claim, or a first run other than the schedule's
law cron_make_refines:
  for +v: Nat
  for +s: Cr.S
  for +p: Nat
  for +sc: Cr.Sched
  for alive: {Cr.has(p, Cr.S.dead(s)) == False{} : Bool}
  {Some{made_jv(CronStore.make_spec(Nat.mul(Cr.first(sc, clock_of(s)), 1n+v)))} == last_jv(last_job(Cr.S.recs(Cr.step(s, Cr.Create{p, sc}))), 1n+v) : Maybe<&2, JV>}

# LAW cron_entry_user_example: anchor: the strings Rust sends for the user's actions: a pause of an active job, a stop of a finished one (left as it is), a delete of a cancelled one (cancelled again), an edit of a paused job (no next run) and of a finished one (locked), a new job, a corrupt file read for an update (moved aside) and for a read (left)
# EXCLUDES: a reply spelled in another order, a stop that cancels a finished job, an edit that wakes a
#   paused job
law cron_entry_user_example:
  {FC.ffi("6,0,1,6,1,10,0,0,") == "1,1,0," : String} &
  {FC.ffi("6,2,1,6,1,10,0,1,") == "0," : String} &
  {FC.ffi("6,3,1,6,1,10,0,2,") == "1,3,0," : String} &
  {FC.ffi("7,1,1,6,1,10,0,1,99,") == "1,1,0," : String} &
  {FC.ffi("7,2,0,0,0,1,9,") == "0," : String} &
  {FC.ffi("8,99,") == "0,99,0," : String} &
  {FC.ffi("9,T") == "T" : String} &
  {FC.ffi("9,F") == "F" : String}
