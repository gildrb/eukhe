# eukhe: the proof of LAW run_retry_counts_down

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.apred(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +n: Nat, +p: Nat, +m: Nat, +x: Nat) -> {RnState.St.a(RnStep.retry(cfg, True{}, r, c, Nat.sub(m, x), n, p)) == Nat.sub(m, 1n+x) : Nat}:
  match m x:
    case 0n x:
      {==}
    case 1n+v 0n:
      LA.rk.sub0(v)
    case 1n+v 1n+y:
      rk.apred(cfg, r, c, n, p, v, y)

def rk.sub_succ(+v: Nat, +s: Nat, +e: {Nat.is_le(s, v) == True{} : Bool}) -> {1n+Nat.sub(v, s) == Nat.sub(1n+v, s) : Nat}:
  match v s:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      LA.rk.absurd({1n+Nat.sub(0n, 1n+y) == Nat.sub(1n, 1n+y) : Nat}, e)
    case 1n+u 0n:
      {==}
    case 1n+u 1n+y:
      rk.sub_succ(u, y, e)

def rk.ra(+retries: Nat, +b: Nat, +notes: Nat, +e: {Nat.is_le(notes, b) == True{} : Bool}) -> {Nat.sub(retries, 1n+Nat.sub(Nat.sub(1n+b, 1n), notes)) == Nat.sub(retries, Nat.sub(Nat.sub(2n+b, 1n), notes)) : Nat}:
  %LA.rk.sub0(b) : {Nat.sub(retries, 1n+Nat.sub(_, notes)) == Nat.sub(retries, Nat.sub(1n+b, notes)) : Nat}
  %rk.sub_succ(b, notes, e) : {Nat.sub(retries, 1n+Nat.sub(b, notes)) == Nat.sub(retries, _) : Nat}
  {==}

def rk.run_retry_counts_down(+l: RnDecision.Lim, +t: RnDecision.At, +e: {Nat.is_le(1n+RnDecision.At.notes(t), RnDecision.At.attempt(t)) == True{} : Bool}, +r: Nat, +c: Nat, +p: Nat) -> {RnState.St.a(RnStep.retry(RnDecision.Lim.cfg(l), True{}, r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.a(l, Run.rust.retried_next(t)) : Nat}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          match attempt:
            case 0n:
              LA.rk.absurd({RnState.St.a(RnStep.retry(RnState.Cfg{rounds, wait, retries, most}, True{}, r, c, Nat.sub(retries, Nat.sub(Nat.sub(0n, 1n), notes)), Nat.sub(most, notes), p)) == Nat.sub(retries, Nat.sub(Nat.sub(1n, 1n), notes)) : Nat}, e)
            case 1n++b:
              Equal.trans(Nat, RnState.St.a(RnStep.retry(RnState.Cfg{rounds, wait, retries, most}, True{}, r, c, Nat.sub(retries, Nat.sub(Nat.sub(1n+b, 1n), notes)), Nat.sub(most, notes), p)), Nat.sub(retries, 1n+Nat.sub(Nat.sub(1n+b, 1n), notes)), Nat.sub(retries, Nat.sub(Nat.sub(2n+b, 1n), notes)), rk.apred(RnState.Cfg{rounds, wait, retries, most}, r, c, Nat.sub(most, notes), p, retries, Nat.sub(Nat.sub(1n+b, 1n), notes)), rk.ra(retries, b, notes, e))

def Run.run_retry_counts_down(l, t, e, r, c, p):
  rk.run_retry_counts_down(l, t, e, r, c, p)
