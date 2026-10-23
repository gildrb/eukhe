# eukhe: the proof of LAW run_round_counts_down

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.rpred_t(+cfg: RnState.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +m: Nat, +x: Nat) -> {RnState.St.r(RnStep.round(cfg, True{}, Nat.sub(m, x), c, a, n, p)) == Nat.sub(m, 1n+x) : Nat}:
  match m x:
    case 0n x:
      {==}
    case 1n+v 0n:
      LA.rk.sub0(v)
    case 1n+v 1n+y:
      rk.rpred_t(cfg, c, a, n, p, v, y)

def rk.rpred_f(+cfg: RnState.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +m: Nat, +x: Nat) -> {RnState.St.r(RnStep.round(cfg, False{}, Nat.sub(m, x), c, a, n, p)) == Nat.sub(m, 1n+x) : Nat}:
  match m x:
    case 0n x:
      {==}
    case 1n+v 0n:
      LA.rk.sub0(v)
    case 1n+v 1n+y:
      rk.rpred_f(cfg, c, a, n, p, v, y)

def rk.run_round_counts_down(+l: RnDecision.Lim, +count: Nat, +reset: Bool, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {RnState.St.r(RnStep.tools(RnDecision.Lim.cfg(l), RnDecision.fin.of(False{}, reset), RnDecision.Lim.r(l, count), c, a, n, p)) == RnDecision.Lim.r(l, 1n+count) : Nat}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match reset:
        case True{}:
          rk.rpred_t(RnState.Cfg{rounds, wait, retries, most}, c, a, n, p, Nat.sub(rounds, 1n), count)
        case False{}:
          rk.rpred_f(RnState.Cfg{rounds, wait, retries, most}, c, a, n, p, Nat.sub(rounds, 1n), count)

def Run.run_round_counts_down(l, count, reset, c, a, n, p):
  rk.run_round_counts_down(l, count, reset, c, a, n, p)
