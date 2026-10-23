# eukhe: the proof of LAW retry_wait_within_cap

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def rx.not_gt_of_le(c: Cmp, e: {Cmp.is_le(c) == True{} : Bool}) -> {Cmp.is_gt(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      LLogicLogic.rp.absurdF({True{} == False{} : Bool}, e)

# (R2) The wait, exactly
# ----------------------

def rx.not_over(over: Bool, +jitter: Nat, +s: Nat, +cap: Nat, e: {over == False{} : Bool}) -> {R.wait.server(over, jitter, s, cap) == R.After{Nat.max(jitter, s)} : R.Delay}:
  match over:
    case True{}:
      LLogicLogic.rp.absurdT({R.wait.server(True{}, jitter, s, cap) == R.After{Nat.max(jitter, s)} : R.Delay}, e)
    case False{}:
      {==}

def wait_within_cap(+jitter: Nat, +s: Nat, +cap: Nat, within: {Nat.is_le(s, cap) == True{} : Bool}) -> {R.wait(jitter, Some{s}, cap) == R.After{Nat.max(jitter, s)} : R.Delay}:
  rx.not_over(Bool.and(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap)), jitter, s, cap, LA.rx.and_f(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap), rx.not_gt_of_le(Nat.cmp(s, cap), within)))

def Retry.retry_wait_within_cap(jitter, s, cap, within):
  wait_within_cap(jitter, s, cap, within)
