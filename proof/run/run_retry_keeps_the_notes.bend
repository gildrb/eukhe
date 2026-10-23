# eukhe: the proof of LAW run_retry_keeps_the_notes

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

def rk.rn(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +n: Nat, +p: Nat, +a: Nat) -> {n == RnState.St.n(RnStep.retry(cfg, True{}, r, c, a, n, p)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      {==}

def rk.run_retry_keeps_the_notes(+l: RnDecision.Lim, +t: RnDecision.At, +r: Nat, +c: Nat, +p: Nat) -> {RnState.St.n(RnStep.retry(RnDecision.Lim.cfg(l), True{}, r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.n(l, Run.rust.retried_next(t)) : Nat}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          Equal.sym(Nat, Nat.sub(most, notes), RnState.St.n(RnStep.retry(RnState.Cfg{rounds, wait, retries, most}, True{}, r, c, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(most, notes), p)), rk.rn(RnState.Cfg{rounds, wait, retries, most}, r, c, Nat.sub(most, notes), p, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))))

def Run.run_retry_keeps_the_notes(l, t, r, c, p):
  rk.run_retry_keeps_the_notes(l, t, r, c, p)
