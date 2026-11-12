# eukhe: the proof of LAW retry_wait_zero_step
# A base of 0 doubles to 0, and a cap of 0 caps every step at 0: the step
# is 0 (rz.step_zero), and the jitter under a step of 0 is 0.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def rz.min_zero(x: Nat) -> {Nat.min(x, 0n) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      {==}

def rz.step_zero(b: Nat, +k: Nat, c: Nat, none: {Bool.or(Nat.is_eq(b, 0n), Nat.is_eq(c, 0n)) == True{} : Bool}) -> {Nat.min(Retry.rs.twice(k, b), c) == 0n : Nat}:
  match b:
    case 0n:
      %LA.rx.twice_zero(k) : {Nat.min(_, c) == 0n : Nat}
      {==}
    case 1n+bp:
      match c:
        case 0n:
          rz.min_zero(Retry.rs.twice(k, 1n+bp))
        case 1n+cp:
          LLogicLogic.rp.absurdF({Nat.min(Retry.rs.twice(k, 1n+bp), 1n+cp) == 0n : Nat}, none)

def zero_step(+base: Nat, +attempt: Nat, +cap: Nat, +draw: Nat, none: {Bool.or(Nat.is_eq(base, 0n), Nat.is_eq(cap, 0n)) == True{} : Bool}) -> {R.retry_wait(base, attempt, cap, draw, None{}) == R.After{0n} : R.Delay}:
  +S = Retry.rs.step(base, attempt, cap)
  Equal.trans(R.Delay, R.retry_wait(base, attempt, cap, draw, None{}), R.After{R.jitter.draw(S, draw)}, R.After{0n}, LA.rx.wait_of(base, attempt, cap, draw), Equal.cong(Nat, R.Delay, x => R.After{R.jitter.draw(x, draw)}, S, 0n, rz.step_zero(base, Nat.sub(attempt, 1n), cap, none)))

def Retry.retry_wait_zero_step(base, attempt, cap, draw, none):
  zero_step(base, attempt, cap, draw, none)
