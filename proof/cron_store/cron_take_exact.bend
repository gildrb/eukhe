# eukhe: the proof of LAW cron_take_exact
# A case split on the facts the pass reads; the comparison of the next run with the due time is the same term on both sides (cx.take_due takes it as a Bool).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def cx.take_due(b: Bool, c: Bool, p: CS.Plan, +n: Nat) -> {CS.take.due(b, c, p, n) == CronStore.take_spec.due(b, c, p, n) : CS.Took}:
  match b c p:
    case False{} _ _:
      {==}
    case True{} True{} CS.POnce{}:
      {==}
    case True{} True{} CS.PEvery{ms}:
      {==}
    case True{} True{} CS.PRule{}:
      {==}
    case True{} False{} CS.POnce{}:
      {==}
    case True{} False{} CS.PEvery{ms}:
      {==}
    case True{} False{} CS.PRule{}:
      {==}

def cx.take(f: CS.Fact, c: Bool, +d: Nat, +n: Nat) -> {CS.take(f, c, d, n) == CronStore.take_spec(f, c, d, n) : CS.Took}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          match nx:
            case None{}:
              {==}
            case Some{+m}:
              cx.take_due(Nat.is_le(m, d), c, p, n)
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def CronStore.cron_take_exact(f, c, d, n):
  cx.take(f, c, d, n)
