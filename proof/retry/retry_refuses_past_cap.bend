# eukhe: the proof of LAW retry_refuses_past_cap

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base.bend as L

def rp.refuse(over: Bool, +jitter: Nat, +s: Nat, +cap: Nat, e: {over == True{} : Bool}) -> {R.wait.server(over, jitter, s, cap) == R.Refused{s, cap} : R.Delay}:
  match over:
    case True{}:
      {==}
    case False{}:
      L.rp.absurdF({R.wait.server(False{}, jitter, s, cap) == R.Refused{s, cap} : R.Delay}, e)

def refuses_past_cap(+jitter: Nat, +s: Nat, +cap: Nat, capped: {Nat.is_gt(cap, 0n) == True{} : Bool}, over: {Nat.is_gt(s, cap) == True{} : Bool}) -> {R.wait(jitter, Some{s}, cap) == R.Refused{s, cap} : R.Delay}:
  rp.refuse(Bool.and(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap)), jitter, s, cap, L.rp.and_tt(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap), capped, over))

def Retry.retry_refuses_past_cap(jitter, s, cap, capped, over):
  refuses_past_cap(jitter, s, cap, capped, over)
