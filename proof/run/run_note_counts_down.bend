# eukhe: the proof of LAW run_note_counts_down

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.npred(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +a: Nat, +p: Nat, +m: Nat, +x: Nat) -> {Rn.St.n(Rn.note(cfg, r, c, a, Nat.sub(m, x), p)) == Nat.sub(m, 1n+x) : Nat}:
  match m x:
    case 0n x:
      {==}
    case 1n+v 0n:
      LA.rk.sub0(v)
    case 1n+v 1n+y:
      rk.npred(cfg, r, c, a, p, v, y)

def rk.run_note_counts_down(+l: Rn.Lim, +t: Rn.At, +r: Nat, +c: Nat, +p: Nat) -> {Rn.St.n(Rn.note(Rn.Lim.cfg(l), r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.n(l, Run.rust.noted_next(t)) : Nat}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          rk.npred(Rn.Cfg{rounds, wait, retries, most}, r, c, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), p, most, notes)

def Run.run_note_counts_down(l, t, r, c, p):
  rk.run_note_counts_down(l, t, r, c, p)
