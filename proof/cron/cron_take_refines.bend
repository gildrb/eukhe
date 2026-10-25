# eukhe: the proof of LAW cron_take_refines
# A job that is not active, or has no next run, stays on both sides. An
# active job with a next run n: the spec compares n * u with c * u, which
# is n compared with c (LSc.crsc.le_mul); a due job rolls its next run to
# the clock plus its interval, added in units by the spec and scaled whole
# by the model (LSc.crsc.dist), and is claimed by p at its next run when no
# claim is on record.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ./base/scale.bend as LSc

def crt.roll(+v: Nat, +c: Nat, s: Cr.Sched) -> {CronStore.next_spec(Cron.plan_of(s, 1n+v), Nat.mul(c, 1n+v)) == CronStore.next_of_spec(Cron.scale_opt(Cr.adv(s, c), 1n+v)) : CS.Next}:
  match s:
    case Cr.Once{d}:
      {==}
    case Cr.Every{+k}:
      %LSc.crsc.dist(c, 1n+k, 1n+v) : {CS.NAt{_} == CS.NAt{Nat.mul(Nat.add(c, 1n+k), 1n+v)} : CS.Next}
      {==}

def crt.due(b: Bool, +v: Nat, +p: Nat, +c: Nat, +i: Nat, +s: Cr.Sched, +n: Nat, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>) -> {Cron.took_view(CronStore.take_spec.due(b, Cron.claimed_of(Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h}), Cron.plan_of(s, 1n+v), Nat.mul(c, 1n+v)), Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h}, p, 1n+v) == Cron.view(Cr.take.due(b, p, c, i, s, n, k, cl, rs, ss, h), 1n+v) : Cron.View()}:
  match b:
    case False{}:
      {==}
    case True{}:
      match cl:
        case None{}:
          %crt.roll(v, c, s) : {(Cr.Active{}, (CronStore.next_spec(Cron.plan_of(s, 1n+v), Nat.mul(c, 1n+v)), (k, Some{Cr.Claim{Nat.mul(n, 1n+v), p}}))) == (Cr.Active{}, (_, (k, Some{Cr.Claim{Nat.mul(n, 1n+v), p}}))) : Cron.View()}
          {==}
        case Some{+x}:
          %crt.roll(v, c, s) : {(Cr.Active{}, (CronStore.next_spec(Cron.plan_of(s, 1n+v), Nat.mul(c, 1n+v)), (k, Cron.scale_claim(Some{x}, 1n+v)))) == (Cr.Active{}, (_, (k, Cron.scale_claim(Some{x}, 1n+v)))) : Cron.View()}
          {==}

def Cron.cron_take_refines(v, p, c, j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              {==}
            case Some{+n}:
              %LSc.crsc.le_mul(n, c, v) : {Cron.took_view(CronStore.take_spec.due(_, Cron.claimed_of(Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h}), Cron.plan_of(s, 1n+v), Nat.mul(c, 1n+v)), Cr.Job{i, s, Cr.Active{}, Some{n}, k, cl, rs, ss, h}, p, 1n+v) == Cron.view(Cr.take.due(Nat.is_le(n, c), p, c, i, s, n, k, cl, rs, ss, h), 1n+v) : Cron.View()}
              crt.due(Nat.is_le(n, c), v, p, c, i, s, n, k, cl, rs, ss, h)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}
