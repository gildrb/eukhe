# eukhe: the proof of LAW run_round_is_the_rust_rule

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

def rk.lt_pred(+m: Nat, +x: Nat) -> {Nat.is_lt(x, Nat.sub(m, 1n)) == Nat.is_lt(1n+x, m) : Bool}:
  match m:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+y:
          {==}
    case 1n+v:
      match v:
        case 0n:
          {==}
        case 1n+u:
          {==}

def rk.round_t(+cfg: RnState.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, +m: Nat, +x: Nat) -> {RnDecision.End.ph(RnState.Resets{}, k, RnState.St.ph(RnStep.round(cfg, True{}, Nat.sub(m, x), c, a, n, p))) == Run.rust.next(Nat.is_lt(x, m), True{}, k) : RnDecision.End}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.round_t(cfg, c, a, n, p, k, v, y)

def rk.round_f(+cfg: RnState.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, +m: Nat, +x: Nat) -> {RnDecision.End.ph(RnState.Goes{}, k, RnState.St.ph(RnStep.round(cfg, False{}, Nat.sub(m, x), c, a, n, p))) == Run.rust.next(Nat.is_lt(x, m), False{}, k) : RnDecision.End}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.round_f(cfg, c, a, n, p, k, v, y)

def rk.run_round_is_the_rust_rule(+l: RnDecision.Lim, +count: Nat, +stops: Bool, +reset: Bool) -> {RnDecision.decide.round(l, count, stops, reset) == Run.rust.round_end(l, count, stops, reset) : RnDecision.End}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match stops reset:
        case True{} reset:
          {==}
        case False{} True{}:
          %rk.lt_pred(rounds, count) : {RnDecision.End.ph(RnState.Resets{}, count, RnState.St.ph(RnStep.round(RnState.Cfg{rounds, wait, retries, most}, True{}, Nat.sub(Nat.sub(rounds, 1n), count), 0n, 0n, 0n, 0n))) == Run.rust.next(_, True{}, count) : RnDecision.End}
          rk.round_t(RnState.Cfg{rounds, wait, retries, most}, 0n, 0n, 0n, 0n, count, Nat.sub(rounds, 1n), count)
        case False{} False{}:
          %rk.lt_pred(rounds, count) : {RnDecision.End.ph(RnState.Goes{}, count, RnState.St.ph(RnStep.round(RnState.Cfg{rounds, wait, retries, most}, False{}, Nat.sub(Nat.sub(rounds, 1n), count), 0n, 0n, 0n, 0n))) == Run.rust.next(_, False{}, count) : RnDecision.End}
          rk.round_f(RnState.Cfg{rounds, wait, retries, most}, 0n, 0n, 0n, 0n, count, Nat.sub(rounds, 1n), count)

def Run.run_round_is_the_rust_rule(l, count, stops, reset):
  rk.run_round_is_the_rust_rule(l, count, stops, reset)
