# eukhe: the proof of LAW retry_after_respected

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry

# (R2) The wait
# -------------

def rp.after(over: Bool, +jitter: Nat, +s: Nat, +cap: Nat) -> {R.Delay.respects(R.wait.server(over, jitter, s, cap), s) == True{} : Bool}:
  match over:
    case True{}:
      {==}
    case False{}:
      Nat.max_ge_r(jitter, s)

def after_respected(+jitter: Nat, +s: Nat, +cap: Nat) -> {R.Delay.respects(R.wait(jitter, Some{s}, cap), s) == True{} : Bool}:
  rp.after(Bool.and(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap)), jitter, s, cap)

def Retry.retry_after_respected(jitter, s, cap):
  after_respected(jitter, s, cap)
