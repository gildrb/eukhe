# eukhe: the proof of LAW cron_finish_counts_run
# p runs the job and holds its claim: the premises take the model's finish
# step through Cr.finish.run and Cr.finish.claim to Cr.finish.own, with p
# out of the runs (the model's Cr.drop is the spec's drop_spec,
# LCj.cj.drop). Then a case split on the status, the result and the
# schedule: the model counts what the store's answer names; a failure of
# a repeating job is counted under the cap and at it, by both (cfc.fail).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_step.bend as CronStep
import ../../laws/cron_job.bend as CronJob
import ./base.bend as LCj

def cfc.eq_refl(p: Nat) -> {True{} == Nat.is_eq(p, p) : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      cfc.eq_refl(q)

def cfc.fail(b: Bool, +c: Nat, +i: Nat, +n: Nat, +nx: Maybe<&2, Nat>, +k2: Nat, +rs2: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, -nx2: Maybe<&2, Nat>, -now: Nat, -u: Nat) -> {CronJob.rest_spec(Cr.finish.fail(b, c, i, Cr.Every{n}, nx, k2, rs2, ss, Cr.MLoss{} <> h)) == CronJob.Rest{i, Cr.Every{n}, rs2, ss, CronJob.counted_spec(CronStore.finish_spec.fail(b, nx2, k2, now, u), True{}, h)} : CronJob.Rest}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# after the claim is released: a case split on the status, the result and
# the schedule
def cfc.own(st: Cr.Status, o: Cr.Out, s: Cr.Sched, +v: Nat, +p: Nat, +c: Nat, +x: Nat, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {CronJob.rest_spec(Cr.finish.own(True{}, Cr.Claim{x, p}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)) == CronJob.Rest{i, s, Cr.drop(p, rs), ss, CronJob.counted_spec(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cron.failed_of(o), h)} : CronJob.Rest}:
  match st:
    case Cr.Active{}:
      match o:
        case Cr.Win{}:
          match s:
            case Cr.Once{d}:
              {==}
            case Cr.Every{n}:
              {==}
        case Cr.Skip{}:
          match s:
            case Cr.Once{d}:
              {==}
            case Cr.Every{n}:
              {==}
        case Cr.Loss{}:
          match s:
            case Cr.Once{d}:
              {==}
            case Cr.Every{+n}:
              cfc.fail(Nat.is_lt(1n+k, 8n), c, i, n, nx, 1n+k, Cr.drop(p, rs), ss, h, Cron.scale_opt(nx, 1n+v), Nat.mul(c, 1n+v), 1n+v)
    case Cr.Paused{}:
      {==}
    case Cr.Finished{}:
      {==}
    case Cr.Cancelled{}:
      {==}

def cfc.main(+v: Nat, +p: Nat, +c: Nat, +o: Cr.Out, +x: Nat, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, run: {Cr.has(p, rs) == True{} : Bool}, own: {cl == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}) -> {CronJob.rest_spec(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, cl, rs, ss, h})) == CronJob.Rest{i, s, CronStep.drop_spec(p, rs), ss, CronJob.counted_spec(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cron.failed_of(o), h)} : CronJob.Rest}:
  %Equal.sym(Bool, Cr.has(p, rs), True{}, run) : {CronJob.rest_spec(Cr.finish.run(_, p, c, o, i, s, st, nx, k, cl, rs, ss, h)) == CronJob.Rest{i, s, CronStep.drop_spec(p, rs), ss, CronJob.counted_spec(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cron.failed_of(o), h)} : CronJob.Rest}
  %Equal.sym(Maybe<&2, Cr.Claim>, cl, Some{Cr.Claim{x, p}}, own) : {CronJob.rest_spec(Cr.finish.claim(_, p, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)) == CronJob.Rest{i, s, CronStep.drop_spec(p, rs), ss, CronJob.counted_spec(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cron.failed_of(o), h)} : CronJob.Rest}
  %cfc.eq_refl(p) : {CronJob.rest_spec(Cr.finish.own(_, Cr.Claim{x, p}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)) == CronJob.Rest{i, s, CronStep.drop_spec(p, rs), ss, CronJob.counted_spec(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cron.failed_of(o), h)} : CronJob.Rest}
  %LCj.cj.drop(p, rs) : {CronJob.rest_spec(Cr.finish.own(True{}, Cr.Claim{x, p}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h)) == CronJob.Rest{i, s, _, ss, CronJob.counted_spec(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cron.failed_of(o), h)} : CronJob.Rest}
  cfc.own(st, o, s, v, p, c, x, i, nx, k, rs, ss, h)

def CronJob.cron_finish_counts_run(v, p, c, o, x, j, run, own):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      cfc.main(v, p, c, o, x, i, s, st, nx, k, cl, rs, ss, h, run, own)
