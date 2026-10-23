# eukhe: the proof of LAW run_note_keeps_the_retries

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def rk.na(+cfg: Rn.Cfg, +r: Nat, +c: Nat, +a: Nat, +p: Nat, +n: Nat) -> {a == Rn.St.a(Rn.note(cfg, r, c, a, n, p)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def rk.s1(+x: Nat, +y: Nat) -> {Nat.sub(Nat.sub(x, 1n), y) == Nat.sub(Nat.sub(1n+x, 1n), 1n+y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+u:
      match u:
        case 0n:
          {==}
        case 1n+v:
          {==}

def rk.run_note_keeps_the_retries(+l: Rn.Lim, +t: Rn.At, +r: Nat, +c: Nat, +p: Nat) -> {Rn.St.a(Rn.note(Rn.Lim.cfg(l), r, c, Rn.At.a(l, t), Rn.At.n(l, t), p)) == Rn.At.a(l, Laws.rust.noted_next(t)) : Nat}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case Rn.At{+attempt, +notes, +waited, +compacted}:
          +cfg = {Rn.Cfg{rounds, wait, retries, most} : Rn.Cfg}
          +a = Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))
          %rk.na(cfg, r, c, a, p, Nat.sub(most, notes)) : {_ == Nat.sub(retries, Nat.sub(Nat.sub(1n+attempt, 1n), 1n+notes)) : Nat}
          %rk.s1(attempt, notes) : {a == Nat.sub(retries, _) : Nat}
          {==}

def Laws.run_note_keeps_the_retries(l, t, r, c, p):
  rk.run_note_keeps_the_retries(l, t, r, c, p)
