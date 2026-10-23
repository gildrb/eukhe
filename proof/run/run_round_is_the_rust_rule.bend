# eukhe: the proof of LAW run_round_is_the_rust_rule

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

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

def rk.round_t(+cfg: Rn.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, +m: Nat, +x: Nat) -> {Rn.End.ph(Rn.Resets{}, k, Rn.St.ph(Rn.round(cfg, True{}, Nat.sub(m, x), c, a, n, p))) == Laws.rust.next(Nat.is_lt(x, m), True{}, k) : Rn.End}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.round_t(cfg, c, a, n, p, k, v, y)

def rk.round_f(+cfg: Rn.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +k: Nat, +m: Nat, +x: Nat) -> {Rn.End.ph(Rn.Goes{}, k, Rn.St.ph(Rn.round(cfg, False{}, Nat.sub(m, x), c, a, n, p))) == Laws.rust.next(Nat.is_lt(x, m), False{}, k) : Rn.End}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+v 1n+y:
      rk.round_f(cfg, c, a, n, p, k, v, y)

def rk.run_round_is_the_rust_rule(+l: Rn.Lim, +count: Nat, +stops: Bool, +reset: Bool) -> {Rn.decide.round(l, count, stops, reset) == Laws.rust.round_end(l, count, stops, reset) : Rn.End}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match stops reset:
        case True{} reset:
          {==}
        case False{} True{}:
          %rk.lt_pred(rounds, count) : {Rn.End.ph(Rn.Resets{}, count, Rn.St.ph(Rn.round(Rn.Cfg{rounds, wait, retries, most}, True{}, Nat.sub(Nat.sub(rounds, 1n), count), 0n, 0n, 0n, 0n))) == Laws.rust.next(_, True{}, count) : Rn.End}
          rk.round_t(Rn.Cfg{rounds, wait, retries, most}, 0n, 0n, 0n, 0n, count, Nat.sub(rounds, 1n), count)
        case False{} False{}:
          %rk.lt_pred(rounds, count) : {Rn.End.ph(Rn.Goes{}, count, Rn.St.ph(Rn.round(Rn.Cfg{rounds, wait, retries, most}, False{}, Nat.sub(Nat.sub(rounds, 1n), count), 0n, 0n, 0n, 0n))) == Laws.rust.next(_, False{}, count) : Rn.End}
          rk.round_f(Rn.Cfg{rounds, wait, retries, most}, 0n, 0n, 0n, 0n, count, Nat.sub(rounds, 1n), count)

def Laws.run_round_is_the_rust_rule(l, count, stops, reset):
  rk.run_round_is_the_rust_rule(l, count, stops, reset)
