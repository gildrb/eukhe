# eukhe: the laws of area cron (the model's step, pinned)
#
# The D2 laws of laws/cron.bend speak of the model's step Cr.step (and
# Cr.run, its fold); the refines laws of laws/cron.bend and
# laws/cron_user.bend tie the per-job steps (Cr.take, Cr.recover,
# Cr.finish, Cr.cancel, Cr.resume, Cr.pause, Cr.stop, Cr.delete, Cr.edit)
# to the store's decisions. A fresh blind adversary made Cr.step change
# the state only on a Create by a live process: every D2 law still held,
# and no law made Cr.step call the per-job steps. Here Cr.step is pinned,
# for every state and every event, to a spec of what the event does to
# the jobs file: which per-job step each record takes, which events of a
# dead process do nothing, which events read the file for an update (a
# corrupt file is moved aside first), the clock, the ids, the records of
# another writer, a corrupt file.
#
# The spec reads Cr.has and Cr.Job.id, both pinned for every input by
# cron_terms_exact (laws/cron_terms.bend) to has_spec and job_id_spec.

import Base
import ../bend/cron.bend as Cr

# Terms
# -----

# the first run of a new job made at clock c: a one-shot Once{d} 1+d
# minutes later, an interval Every{k} 1+k minutes later
def first_spec(sc: Cr.Sched, +c: Nat) -> Nat:
  match sc:
    case Cr.Once{d}:
      Nat.add(c, 1n+d)
    case Cr.Every{k}:
      Nat.add(c, 1n+k)

# a new job of id n made at clock c: active, its first run, no failures in
# a row, no claim, no run, no occurrence started, no result counted
def new_job_spec(+n: Nat, +sc: Cr.Sched, +c: Nat) -> Cr.Job:
  Cr.Job{n, sc, Cr.Active{}, Some{first_spec(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}

# the files moved aside after an update reads the file: a corrupt file is
# moved aside first (the newest first)
def healed_spec(bad: Maybe<&2, Nat>, aside: List<&2, Nat>) -> List<&2, Nat>:
  match bad:
    case None{}:
      aside
    case Some{t}:
      t <> aside

def keep_run_spec(gone: Bool, x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match gone:
    case True{}:
      rest
    case False{}:
      x <> rest

# the runs xs without process p
def drop_spec(+p: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      keep_run_spec(Nat.is_eq(x, p), x, drop_spec(p, t))

# a job whose run by p ends without a result (p unwinds its pass or dies):
# p no longer runs it; nothing else changes
def unrun_spec(+p: Nat, j: Cr.Job) -> Cr.Job:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      Cr.Job{i, s, st, nx, k, cl, drop_spec(p, rs), ss, h}

# job j takes a when it is the job named (b), else stays
def named_spec(b: Bool, a: Cr.Job, j: Cr.Job) -> Cr.Job:
  match b:
    case True{}:
      a
    case False{}:
      j

# what event e does to one job j, at clock c with the dead processes dead:
# a claim pass and a recovery of p reach every job; a finish of p's run of
# job i and every user action on job i reach job i alone; an unwind or a
# death of p ends p's runs of every job; a new job, time, another writer's
# record and a corrupt file change no job
def job_spec(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job) -> Cr.Job:
  match e:
    case Cr.Create{p, sc}:
      j
    case Cr.Take{p}:
      Cr.take(p, c, j)
    case Cr.Recover{p}:
      Cr.recover(p, dead, j)
    case Cr.Finish{p, i, o}:
      named_spec(Nat.is_eq(Cr.Job.id(j), i), Cr.finish(p, c, o, j), j)
    case Cr.Abort{p}:
      unrun_spec(p, j)
    case Cr.Die{p}:
      unrun_spec(p, j)
    case Cr.Cancel{p, i}:
      named_spec(Nat.is_eq(Cr.Job.id(j), i), Cr.cancel(j), j)
    case Cr.Resume{p, i}:
      named_spec(Nat.is_eq(Cr.Job.id(j), i), Cr.resume(c, j), j)
    case Cr.Tick{d}:
      j
    case Cr.RawJob{t}:
      j
    case Cr.RawClaim{t}:
      j
    case Cr.Corrupt{t}:
      j
    case Cr.Pause{p, i}:
      named_spec(Nat.is_eq(Cr.Job.id(j), i), Cr.pause(j), j)
    case Cr.Stop{p, i}:
      named_spec(Nat.is_eq(Cr.Job.id(j), i), Cr.stop(j), j)
    case Cr.Delete{p, i}:
      named_spec(Nat.is_eq(Cr.Job.id(j), i), Cr.delete(j), j)
    case Cr.Edit{p, i, k}:
      named_spec(Nat.is_eq(Cr.Job.id(j), i), Cr.edit(c, k, j), j)

# the records after e: each job record takes e, in place; a record this
# build cannot read stays with its bytes
def recs_spec(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> List<&2, Cr.Rec>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Cr.Known{job_spec(e, c, dead, j)} <> recs_spec(e, c, dead, t)
        case Cr.Raw{x}:
          Cr.Raw{x} <> recs_spec(e, c, dead, t)

# the state after an event of a process: unchanged when it is dead (in
# `dead`), else `after`
def live_spec(dead: Bool, after: Cr.S, before: Cr.S) -> Cr.S:
  match dead:
    case True{}:
      before
    case False{}:
      after

# another writer's record lands only in a file this build can read
def readable_spec(bad: Maybe<&2, Nat>, after: Cr.S, before: Cr.S) -> Cr.S:
  match bad:
    case None{}:
      after
    case Some{t}:
      before

# the state after event e. A new job, a claim pass, a recovery and a
# finish of a live process update the file (a corrupt file moved aside,
# then no longer corrupt); a new job appends its record with the next id;
# an unwind and the user's actions of a live process change the records
# alone; a death changes the records (the dead process runs nothing) and
# adds the process to the dead; time moves the clock; another writer
# appends a record or a claim record to a readable file; a corruption
# leaves a corrupt file with no record and no claim record, the dead, the
# clock, the ids and the files moved aside kept
def step_spec(s: Cr.S, +e: Cr.Ev) -> Cr.S:
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          live_spec(Cr.has(p, dead), Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{new_job_spec(n, sc, c)}]), rd, dead, c, 1n+n, healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Take{+p}:
          live_spec(Cr.has(p, dead), Cr.S{None{}, recs_spec(e, c, dead, rs), rd, dead, c, n, healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Recover{+p}:
          live_spec(Cr.has(p, dead), Cr.S{None{}, recs_spec(e, c, dead, rs), rd, dead, c, n, healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Finish{+p, i, o}:
          live_spec(Cr.has(p, dead), Cr.S{None{}, recs_spec(e, c, dead, rs), rd, dead, c, n, healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Abort{+p}:
          live_spec(Cr.has(p, dead), Cr.S{bad, recs_spec(e, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Die{p}:
          Cr.S{bad, recs_spec(e, c, dead, rs), rd, p <> dead, c, n, aside}
        case Cr.Cancel{+p, i}:
          live_spec(Cr.has(p, dead), Cr.S{bad, recs_spec(e, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Resume{+p, i}:
          live_spec(Cr.has(p, dead), Cr.S{bad, recs_spec(e, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Tick{d}:
          Cr.S{bad, rs, rd, dead, Nat.add(c, d), n, aside}
        case Cr.RawJob{t}:
          readable_spec(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}]), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.RawClaim{t}:
          readable_spec(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Corrupt{t}:
          Cr.S{Some{t}, Nil{}, Nil{}, dead, c, n, aside}
        case Cr.Pause{+p, i}:
          live_spec(Cr.has(p, dead), Cr.S{bad, recs_spec(e, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Stop{+p, i}:
          live_spec(Cr.has(p, dead), Cr.S{bad, recs_spec(e, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Delete{+p, i}:
          live_spec(Cr.has(p, dead), Cr.S{bad, recs_spec(e, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Edit{+p, i, k}:
          live_spec(Cr.has(p, dead), Cr.S{bad, recs_spec(e, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})

# Laws
# ----

# LAW cron_step_exact: from any state, every event changes the jobs file exactly as the spec says: a claim pass, a recovery, a finish, an unwind or a user action of a live process applies the model's per-job step to each job record it reaches (every job, or the job named), keeping every record this build cannot read; a death ends the process's runs and marks it dead; a new job of a live process appends its record with the next id; the events that update the file move a corrupt one aside; time, another writer's records and a corruption change exactly their part; a dead process changes nothing
# EXCLUDES: a step that skips the per-job step of an event (a claim pass, recovery, finish, user action or death that changes nothing), applies it to the wrong job, drops or reorders a record, acts for a dead process, or writes over a corrupt file without moving it aside
law cron_step_exact:
  for +s: Cr.S
  for +e: Cr.Ev
  {Cr.step(s, e) == step_spec(s, e) : Cr.S}

# LAW cron_step_example: anchor: a job made every minute is claimed when due, counts a failure (next run after the 2-minute pause, at minute 3), its run ends; a dead process makes no job; another writer's record is kept after it; and a new job after a corruption moves the corrupt file aside and takes the next id
# EXCLUDES: a step that ignores a claim pass, a finish, a death or an update of a corrupt file
law cron_step_example:
  {Cr.run([Cr.Create{0n, Cr.Every{0n}}, Cr.Tick{1n}, Cr.Take{0n}, Cr.Finish{0n, 0n, Cr.Loss{}}, Cr.Die{1n}, Cr.Create{1n, Cr.Once{0n}}, Cr.RawJob{7n}]) == Cr.S{None{}, [Cr.Known{Cr.Job{0n, Cr.Every{0n}, Cr.Active{}, Some{3n}, 1n, None{}, [], [1n], [Cr.MLoss{}]}}, Cr.Raw{7n}], [], [1n], 1n, 1n, []} : Cr.S} &
  {Cr.run([Cr.Create{0n, Cr.Once{2n}}, Cr.Corrupt{9n}, Cr.Create{0n, Cr.Once{2n}}]) == Cr.S{None{}, [Cr.Known{Cr.Job{1n, Cr.Once{2n}, Cr.Active{}, Some{3n}, 0n, None{}, [], [], []}}], [], [], 0n, 2n, [9n]} : Cr.S}
