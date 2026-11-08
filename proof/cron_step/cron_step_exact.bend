# eukhe: the proof of LAW cron_step_exact
# Each event of the model's step applies, to every record it reaches, the
# per-job step the spec names (cs.job, cs.recs); the dead check, the
# update of a corrupt file, another writer's records and the new job are
# the spec's (cs.live, cs.upd, cs.raw, cs.create).

import Base
import ../../bend/cron.bend as Cr
import ../../laws/cron_step.bend as CronStep

# One job
# -------

def cs.keep(b: Bool, x: Nat, r: List<&2, Nat>) -> {Cr.drop.put(b, x, r) == CronStep.keep_run_spec(b, x, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.drop(+p: Nat, xs: List<&2, Nat>) -> {Cr.drop(p, xs) == CronStep.drop_spec(p, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %cs.drop(p, t) : {Cr.drop.put(Nat.is_eq(x, p), x, Cr.drop(p, t)) == CronStep.keep_run_spec(Nat.is_eq(x, p), x, _) : List<&2, Nat>}
      cs.keep(Nat.is_eq(x, p), x, Cr.drop(p, t))

def cs.unrun(+p: Nat, j: Cr.Job) -> {Cr.unrun(p, j) == CronStep.unrun_spec(p, j) : Cr.Job}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, +rs, ss, h}:
      %cs.drop(p, rs) : {Cr.Job{i, s, st, nx, k, cl, Cr.drop(p, rs), ss, h} == Cr.Job{i, s, st, nx, k, cl, _, ss, h} : Cr.Job}
      {==}

def cs.pick(b: Bool, a: Cr.Job, j: Cr.Job) -> {Cr.job.pick(b, a, j) == CronStep.named_spec(b, a, j) : Cr.Job}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.job(e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job) -> {Cr.job(e, c, dead, j) == CronStep.job_spec(e, c, dead, j) : Cr.Job}:
  match e:
    case Cr.Create{p, sc}:
      {==}
    case Cr.Take{p}:
      {==}
    case Cr.Recover{p}:
      {==}
    case Cr.Finish{p, i, o}:
      cs.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.finish(p, c, o, j), j)
    case Cr.Abort{p}:
      cs.unrun(p, j)
    case Cr.Die{p}:
      cs.unrun(p, j)
    case Cr.Cancel{p, i}:
      cs.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.cancel(j), j)
    case Cr.Resume{p, i}:
      cs.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.resume(c, j), j)
    case Cr.Tick{d}:
      {==}
    case Cr.RawJob{t}:
      {==}
    case Cr.RawClaim{t}:
      {==}
    case Cr.Corrupt{t}:
      {==}
    case Cr.Pause{p, i}:
      cs.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.pause(j), j)
    case Cr.Stop{p, i}:
      cs.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.stop(j), j)
    case Cr.Delete{p, i}:
      cs.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.delete(j), j)
    case Cr.Edit{p, i, k}:
      cs.pick(Nat.is_eq(Cr.Job.id(j), i), Cr.edit(c, k, j), j)

def cs.recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> {Cr.recs(e, c, dead, rs) == CronStep.recs_spec(e, c, dead, rs) : List<&2, Cr.Rec>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          %cs.job(e, c, dead, j) : {Cr.Known{Cr.job(e, c, dead, j)} <> Cr.recs(e, c, dead, t) == Cr.Known{_} <> CronStep.recs_spec(e, c, dead, t) : List<&2, Cr.Rec>}
          %cs.recs(e, c, dead, t) : {Cr.Known{Cr.job(e, c, dead, j)} <> Cr.recs(e, c, dead, t) == Cr.Known{Cr.job(e, c, dead, j)} <> _ : List<&2, Cr.Rec>}
          {==}
        case Cr.Raw{+x}:
          %cs.recs(e, c, dead, t) : {Cr.Raw{x} <> Cr.recs(e, c, dead, t) == Cr.Raw{x} <> _ : List<&2, Cr.Rec>}
          {==}

# The file
# --------

def cs.live(b: Bool, -a1: Cr.S, -a2: Cr.S, -s1: Cr.S, ha: {a1 == a2 : Cr.S}) -> {Cr.step.alive(b, a1, s1) == CronStep.live_spec(b, a2, s1) : Cr.S}:
  match b:
    case False{}:
      ha
    case True{}:
      {==}

def cs.raw(bad: Maybe<&2, Nat>, a: Cr.S, s1: Cr.S) -> {Cr.step.raw(bad, a, s1) == CronStep.readable_spec(bad, a, s1) : Cr.S}:
  match bad:
    case None{}:
      {==}
    case Some{t}:
      {==}

# an update: the records take the event, a corrupt file is moved aside
def cs.upd(bad: Maybe<&2, Nat>, +aside: List<&2, Nat>, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +n: Nat) -> {Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)} == Cr.S{None{}, CronStep.recs_spec(e, c, dead, rs), rd, dead, c, n, CronStep.healed_spec(bad, aside)} : Cr.S}:
  match bad:
    case None{}:
      %cs.recs(e, c, dead, rs) : {Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside} == Cr.S{None{}, _, rd, dead, c, n, aside} : Cr.S}
      {==}
    case Some{+t}:
      %cs.recs(e, c, dead, rs) : {Cr.S{None{}, Cr.recs(e, c, dead, rs), rd, dead, c, n, t <> aside} == Cr.S{None{}, _, rd, dead, c, n, t <> aside} : Cr.S}
      {==}

# a change of the records alone
def cs.kept(+bad: Maybe<&2, Nat>, +aside: List<&2, Nat>, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +n: Nat) -> {Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside} == Cr.S{bad, CronStep.recs_spec(e, c, dead, rs), rd, dead, c, n, aside} : Cr.S}:
  %cs.recs(e, c, dead, rs) : {Cr.S{bad, Cr.recs(e, c, dead, rs), rd, dead, c, n, aside} == Cr.S{bad, _, rd, dead, c, n, aside} : Cr.S}
  {==}

# a new job
def cs.create(bad: Maybe<&2, Nat>, sc: Cr.Sched, +aside: List<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat) -> {Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, Cr.heal(bad, aside)} == Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{CronStep.new_job_spec(n, sc, c)}]), rd, dead, c, 1n+n, CronStep.healed_spec(bad, aside)} : Cr.S}:
  match bad:
    case None{}:
      match sc:
        case Cr.Once{d}:
          {==}
        case Cr.Every{k}:
          {==}
    case Some{t}:
      match sc:
        case Cr.Once{d}:
          {==}
        case Cr.Every{k}:
          {==}

# CronStep

def CronStep.cron_step_exact(s, e):
  match s:
    case Cr.S{+bad, +rs, +rd, +dead, +c, +n, +aside}:
      match e:
        case Cr.Create{+p, +sc}:
          cs.live(Cr.has(p, dead), Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, Cr.heal(bad, aside)}, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{CronStep.new_job_spec(n, sc, c)}]), rd, dead, c, 1n+n, CronStep.healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.create(bad, sc, aside, rs, rd, dead, c, n))
        case Cr.Take{+p}:
          cs.live(Cr.has(p, dead), Cr.S{None{}, Cr.recs(Cr.Take{p}, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, Cr.S{None{}, CronStep.recs_spec(Cr.Take{p}, c, dead, rs), rd, dead, c, n, CronStep.healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.upd(bad, aside, Cr.Take{p}, c, dead, rs, rd, n))
        case Cr.Recover{+p}:
          cs.live(Cr.has(p, dead), Cr.S{None{}, Cr.recs(Cr.Recover{p}, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, Cr.S{None{}, CronStep.recs_spec(Cr.Recover{p}, c, dead, rs), rd, dead, c, n, CronStep.healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.upd(bad, aside, Cr.Recover{p}, c, dead, rs, rd, n))
        case Cr.Finish{+p, +i, +o}:
          cs.live(Cr.has(p, dead), Cr.S{None{}, Cr.recs(Cr.Finish{p, i, o}, c, dead, rs), rd, dead, c, n, Cr.heal(bad, aside)}, Cr.S{None{}, CronStep.recs_spec(Cr.Finish{p, i, o}, c, dead, rs), rd, dead, c, n, CronStep.healed_spec(bad, aside)}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.upd(bad, aside, Cr.Finish{p, i, o}, c, dead, rs, rd, n))
        case Cr.Abort{+p}:
          cs.live(Cr.has(p, dead), Cr.S{bad, Cr.recs(Cr.Abort{p}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, CronStep.recs_spec(Cr.Abort{p}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.kept(bad, aside, Cr.Abort{p}, c, dead, rs, rd, n))
        case Cr.Die{+p}:
          %cs.recs(Cr.Die{p}, c, dead, rs) : {Cr.S{bad, Cr.recs(Cr.Die{p}, c, dead, rs), rd, p <> dead, c, n, aside} == Cr.S{bad, _, rd, p <> dead, c, n, aside} : Cr.S}
          {==}
        case Cr.Cancel{+p, +i}:
          cs.live(Cr.has(p, dead), Cr.S{bad, Cr.recs(Cr.Cancel{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, CronStep.recs_spec(Cr.Cancel{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.kept(bad, aside, Cr.Cancel{p, i}, c, dead, rs, rd, n))
        case Cr.Resume{+p, +i}:
          cs.live(Cr.has(p, dead), Cr.S{bad, Cr.recs(Cr.Resume{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, CronStep.recs_spec(Cr.Resume{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.kept(bad, aside, Cr.Resume{p, i}, c, dead, rs, rd, n))
        case Cr.Tick{d}:
          {==}
        case Cr.RawJob{+t}:
          cs.raw(bad, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Raw{t}]), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.RawClaim{+t}:
          cs.raw(bad, Cr.S{None{}, rs, List.append(&2, Nat, rd, [t]), dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside})
        case Cr.Corrupt{t}:
          {==}
        case Cr.Pause{+p, +i}:
          cs.live(Cr.has(p, dead), Cr.S{bad, Cr.recs(Cr.Pause{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, CronStep.recs_spec(Cr.Pause{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.kept(bad, aside, Cr.Pause{p, i}, c, dead, rs, rd, n))
        case Cr.Stop{+p, +i}:
          cs.live(Cr.has(p, dead), Cr.S{bad, Cr.recs(Cr.Stop{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, CronStep.recs_spec(Cr.Stop{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.kept(bad, aside, Cr.Stop{p, i}, c, dead, rs, rd, n))
        case Cr.Delete{+p, +i}:
          cs.live(Cr.has(p, dead), Cr.S{bad, Cr.recs(Cr.Delete{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, CronStep.recs_spec(Cr.Delete{p, i}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.kept(bad, aside, Cr.Delete{p, i}, c, dead, rs, rd, n))
        case Cr.Edit{+p, +i, +k}:
          cs.live(Cr.has(p, dead), Cr.S{bad, Cr.recs(Cr.Edit{p, i, k}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, CronStep.recs_spec(Cr.Edit{p, i, k}, c, dead, rs), rd, dead, c, n, aside}, Cr.S{bad, rs, rd, dead, c, n, aside}, cs.kept(bad, aside, Cr.Edit{p, i, k}, c, dead, rs, rd, n))
