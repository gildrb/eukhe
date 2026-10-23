# eukhe: the proof of LAW run_note_keeps_the_retries

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

def rk.na(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +p: Nat, +n: Nat) -> {a == RnState.St.a(RnStep.note(cfg, r, c, a, n, p)) : Nat}:
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

def rk.run_note_keeps_the_retries(+l: RnDecision.Lim, +t: RnDecision.At, +r: Nat, +c: Nat, +p: Nat) -> {RnState.St.a(RnStep.note(RnDecision.Lim.cfg(l), r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.a(l, Run.rust.noted_next(t)) : Nat}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          +cfg = {RnState.Cfg{rounds, wait, retries, most} : RnState.Cfg}
          +a = Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes))
          %rk.na(cfg, r, c, a, p, Nat.sub(most, notes)) : {_ == Nat.sub(retries, Nat.sub(Nat.sub(1n+attempt, 1n), 1n+notes)) : Nat}
          %rk.s1(attempt, notes) : {a == Nat.sub(retries, _) : Nat}
          {==}

def Run.run_note_keeps_the_retries(l, t, r, c, p):
  rk.run_note_keeps_the_retries(l, t, r, c, p)
