# eukhe: the proof of LAW run_round_counts_down

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws
import ./base.bend as LA

def rk.rpred_t(+cfg: Rn.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +m: Nat, +x: Nat) -> {Rn.St.r(Rn.round(cfg, True{}, Nat.sub(m, x), c, a, n, p)) == Nat.sub(m, 1n+x) : Nat}:
  match m x:
    case 0n x:
      {==}
    case 1n+v 0n:
      LA.rk.sub0(v)
    case 1n+v 1n+y:
      rk.rpred_t(cfg, c, a, n, p, v, y)

def rk.rpred_f(+cfg: Rn.Cfg, +c: Nat, +a: Nat, +n: Nat, +p: Nat, +m: Nat, +x: Nat) -> {Rn.St.r(Rn.round(cfg, False{}, Nat.sub(m, x), c, a, n, p)) == Nat.sub(m, 1n+x) : Nat}:
  match m x:
    case 0n x:
      {==}
    case 1n+v 0n:
      LA.rk.sub0(v)
    case 1n+v 1n+y:
      rk.rpred_f(cfg, c, a, n, p, v, y)

def rk.run_round_counts_down(+l: Rn.Lim, +count: Nat, +reset: Bool, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {Rn.St.r(Rn.tools(Rn.Lim.cfg(l), Rn.fin.of(False{}, reset), Rn.Lim.r(l, count), c, a, n, p)) == Rn.Lim.r(l, 1n+count) : Nat}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match reset:
        case True{}:
          rk.rpred_t(Rn.Cfg{rounds, wait, retries, most}, c, a, n, p, Nat.sub(rounds, 1n), count)
        case False{}:
          rk.rpred_f(Rn.Cfg{rounds, wait, retries, most}, c, a, n, p, Nat.sub(rounds, 1n), count)

def Laws.run_round_counts_down(l, count, reset, c, a, n, p):
  rk.run_round_counts_down(l, count, reset, c, a, n, p)
