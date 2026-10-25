# eukhe: the proof of LAW cron_finish_exact
# A case split on the status, the result and the schedule; a failure under the cap waits the pause of the model (Cr.delay, the spec's table: cx.delay) after the later of the next run and the pause's end (Cr.later, the spec's: cx.later).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def cx.delay(k: Nat) -> {Cr.delay(k) == CronStore.pause_min_spec(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n+r:
      {==}

def cx.later_pick(b: Bool, n: Nat, w: Nat) -> {Cr.later.pick(b, n, w) == CronStore.later_spec.pick(b, n, w) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cx.later(nx: Maybe<&2, Nat>, +w: Nat) -> {Cr.later(nx, w) == CronStore.later_spec(nx, w) : Nat}:
  match nx:
    case None{}:
      {==}
    case Some{+n}:
      cx.later_pick(Nat.is_lt(n, w), n, w)

def cx.fail(b: Bool, +now: Nat, +nx: Maybe<&2, Nat>, +k: Nat, +u: Nat) -> {CS.finish.fail(b, now, nx, k, u) == CronStore.finish_spec.fail(b, nx, k, now, u) : CS.Fin}:
  match b:
    case True{}:
      %cx.delay(k) : {CS.Ran{Cr.Active{}, CS.NAt{Cr.later(nx, Nat.add(now, Nat.mul(Cr.delay(k), u)))}, k} == CS.Ran{Cr.Active{}, CS.NAt{CronStore.later_spec(nx, Nat.add(now, Nat.mul(_, u)))}, k} : CS.Fin}
      %cx.later(nx, Nat.add(now, Nat.mul(Cr.delay(k), u))) : {CS.Ran{Cr.Active{}, CS.NAt{Cr.later(nx, Nat.add(now, Nat.mul(Cr.delay(k), u)))}, k} == CS.Ran{Cr.Active{}, CS.NAt{_}, k} : CS.Fin}
      {==}
    case False{}:
      {==}

def cx.finish_on(failed: Bool, ran: Bool, p: CS.Plan, nx: Maybe<&2, Nat>, +k: Nat, +now: Nat, +u: Nat) -> {CS.finish.active(CS.outcome(failed, ran), p, nx, k, now, u) == CronStore.finish_spec.on(failed, ran, CronStore.once_spec(p), p, nx, k, now, u) : CS.Fin}:
  match failed ran p:
    case True{} _ CS.POnce{}:
      {==}
    case True{} _ CS.PEvery{ms}:
      cx.fail(Nat.is_lt(1n+k, 8n), now, nx, 1n+k, u)
    case True{} _ CS.PRule{}:
      cx.fail(Nat.is_lt(1n+k, 8n), now, nx, 1n+k, u)
    case False{} True{} CS.POnce{}:
      {==}
    case False{} True{} CS.PEvery{ms}:
      match nx:
        case None{}:
          {==}
        case Some{m}:
          {==}
    case False{} True{} CS.PRule{}:
      match nx:
        case None{}:
          {==}
        case Some{m}:
          {==}
    case False{} False{} CS.POnce{}:
      {==}
    case False{} False{} CS.PEvery{ms}:
      {==}
    case False{} False{} CS.PRule{}:
      {==}

def cx.finish(+u: Nat, f: CS.Fact, ran: Bool, failed: Bool, +now: Nat) -> {CS.finish(u, f, ran, failed, now) == CronStore.finish_spec(u, f, ran, failed, now) : CS.Fin}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          cx.finish_on(failed, ran, p, nx, k, now, u)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def CronStore.cron_finish_exact(u, f, r, b, n):
  cx.finish(u, f, r, b, n)
