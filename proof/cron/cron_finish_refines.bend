# eukhe: the proof of LAW cron_finish_refines
# p runs the job and holds its claim: the model's finish step releases the
# claim and, for an active job, counts the result (the premises take the
# model through `finish.run` and `finish.claim`). Then a case split on the
# status, the result and the schedule: a skip rolls an interval, added in
# units by the spec and scaled whole by the model (LSc.crsc.dist); a failure
# under the cap backs off to the later of the next run and the pause's
# end, which the spec computes on scaled times (crf.later: the order of
# scaled times is the order of the times, LSc.crsc.lt_mul) with the pause in
# minutes the model's (LAn.creq.delay).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ./base/answer.bend as LAn
import ./base/scale.bend as LSc

def crf.eq_refl(p: Nat) -> {True{} == Nat.is_eq(p, p) : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      crf.eq_refl(q)

def crf.pick(b: Bool, +n: Nat, +w: Nat, +u: Nat) -> {Nat.mul(Cr.later.pick(b, n, w), u) == CronStore.later_spec.pick(b, Nat.mul(n, u), Nat.mul(w, u)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the later of two times, scaled, is the later of the two scaled times
def crf.later(nx: Maybe<&2, Nat>, +w: Nat, +v: Nat) -> {Nat.mul(Cr.later(nx, w), 1n+v) == CronStore.later_spec(Cron.scale_opt(nx, 1n+v), Nat.mul(w, 1n+v)) : Nat}:
  match nx:
    case None{}:
      {==}
    case Some{+n}:
      %LSc.crsc.lt_mul(n, w, v) : {Nat.mul(Cr.later.pick(Nat.is_lt(n, w), n, w), 1n+v) == CronStore.later_spec.pick(_, Nat.mul(n, 1n+v), Nat.mul(w, 1n+v)) : Nat}
      crf.pick(Nat.is_lt(n, w), n, w, 1n+v)

def crf.fail(b: Bool, +v: Nat, +c: Nat, +i: Nat, +n: Nat, +nx: Maybe<&2, Nat>, +k2: Nat, +rs2: List<&2, Nat>, +ss: List<&2, Nat>, +h2: List<&2, Cr.Mark>, -j0: Cr.Job) -> {Cron.fin_view(CronStore.finish_spec.fail(b, Cron.scale_opt(nx, 1n+v), k2, Nat.mul(c, 1n+v), 1n+v), j0, 1n+v) == Cron.view(Cr.finish.fail(b, c, i, Cr.Every{n}, nx, k2, rs2, ss, h2), 1n+v) : Cron.View()}:
  match b:
    case True{}:
      %LAn.creq.delay(k2) : {(Cr.Active{}, (CS.NAt{CronStore.later_spec(Cron.scale_opt(nx, 1n+v), Nat.add(Nat.mul(c, 1n+v), Nat.mul(_, 1n+v)))}, (k2, None{}))) == (Cr.Active{}, (CS.NAt{Nat.mul(Cr.later(nx, Nat.add(c, Cr.delay(k2))), 1n+v)}, (k2, None{}))) : Cron.View()}
      %LSc.crsc.dist(c, Cr.delay(k2), 1n+v) : {(Cr.Active{}, (CS.NAt{CronStore.later_spec(Cron.scale_opt(nx, 1n+v), _)}, (k2, None{}))) == (Cr.Active{}, (CS.NAt{Nat.mul(Cr.later(nx, Nat.add(c, Cr.delay(k2))), 1n+v)}, (k2, None{}))) : Cron.View()}
      %crf.later(nx, Nat.add(c, Cr.delay(k2)), v) : {(Cr.Active{}, (CS.NAt{_}, (k2, None{}))) == (Cr.Active{}, (CS.NAt{Nat.mul(Cr.later(nx, Nat.add(c, Cr.delay(k2))), 1n+v)}, (k2, None{}))) : Cron.View()}
      {==}
    case False{}:
      {==}

# after the claim is released: a case split on the status, the result and
# the schedule
def crf.own(st: Cr.Status, o: Cr.Out, s: Cr.Sched, +v: Nat, +p: Nat, +c: Nat, +x: Nat, +i: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cron.fin_view(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, cl, rs, ss, h}, 1n+v) == Cron.view(Cr.finish.own(True{}, Cr.Claim{x, p}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h), 1n+v) : Cron.View()}:
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
            case Cr.Every{+n}:
              %LSc.crsc.dist(c, 1n+n, 1n+v) : {(Cr.Active{}, (CS.NAt{_}, (k, None{}))) == (Cr.Active{}, (CS.NAt{Nat.mul(Nat.add(c, 1n+n), 1n+v)}, (k, None{}))) : Cron.View()}
              {==}
        case Cr.Loss{}:
          match s:
            case Cr.Once{d}:
              {==}
            case Cr.Every{n}:
              crf.fail(Nat.is_lt(1n+k, 8n), v, c, i, n, nx, 1n+k, Cr.drop(p, rs), ss, Cr.MLoss{} <> h, Cr.Job{i, Cr.Every{n}, Cr.Active{}, nx, k, cl, rs, ss, h})
    case Cr.Paused{}:
      {==}
    case Cr.Finished{}:
      {==}
    case Cr.Cancelled{}:
      {==}

def crf.main(+v: Nat, +p: Nat, +c: Nat, +o: Cr.Out, +x: Nat, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, run: {Cr.has(p, rs) == True{} : Bool}, own: {cl == Some{Cr.Claim{x, p}} : Maybe<&2, Cr.Claim>}) -> {Cron.fin_view(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, cl, rs, ss, h}, 1n+v) == Cron.view(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, cl, rs, ss, h}), 1n+v) : Cron.View()}:
  %Equal.sym(Bool, Cr.has(p, rs), True{}, run) : {Cron.fin_view(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, cl, rs, ss, h}, 1n+v) == Cron.view(Cr.finish.run(_, p, c, o, i, s, st, nx, k, cl, rs, ss, h), 1n+v) : Cron.View()}
  %Equal.sym(Maybe<&2, Cr.Claim>, cl, Some{Cr.Claim{x, p}}, own) : {Cron.fin_view(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, cl, rs, ss, h}, 1n+v) == Cron.view(Cr.finish.claim(_, p, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h), 1n+v) : Cron.View()}
  %crf.eq_refl(p) : {Cron.fin_view(CronStore.finish_spec(1n+v, CS.Fact{st, Cron.plan_of(s, 1n+v), Cron.scale_opt(nx, 1n+v), k}, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, cl, rs, ss, h}, 1n+v) == Cron.view(Cr.finish.own(_, Cr.Claim{x, p}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h), 1n+v) : Cron.View()}
  crf.own(st, o, s, v, p, c, x, i, nx, k, cl, rs, ss, h)

def Cron.cron_finish_refines(v, p, c, o, x, j, run, own):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      crf.main(v, p, c, o, x, i, s, st, nx, k, cl, rs, ss, h, run, own)
