# eukhe: the proof of LAW run_retry_keeps_the_notes

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def rk.rn(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +n: Nat, +p: Nat, +a: Nat) -> {n == Rn.St.n(Rn.retry(cfg, True{}, r, c, a, n, p)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      {==}

def rk.run_retry_keeps_the_notes(+l: Rn.Lim, +t: Rn.At, +r: Nat, +c: Nat, +p: Nat) -> {Rn.St.n(Rn.retry(Rn.Lim.cfg(l), True{}, r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.n(l, Run.rust.retried_next(t)) : Nat}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          Equal.sym(Nat, Nat.sub(most, notes), Rn.St.n(Rn.retry(Rn.Cfg{rounds, wait, retries, most}, True{}, r, c, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), Nat.sub(most, notes), p)), rk.rn(Rn.Cfg{rounds, wait, retries, most}, r, c, Nat.sub(most, notes), p, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))))

def Run.run_retry_keeps_the_notes(l, t, r, c, p):
  rk.run_retry_keeps_the_notes(l, t, r, c, p)
