# eukhe: the proof of LAW retry_wait_server_past_cap
# The wait of a retry is the wait of its jitter (retry_wait unfolds to
# wait), which refuses a server wait past a positive cap
# (retry_refuses_past_cap), whatever the jitter.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./retry_refuses_past_cap.bend as PRetryRefusesPastCap

def server_past_cap(+base: Nat, +attempt: Nat, +cap: Nat, +draw: Nat, +s: Nat, capped: {Nat.is_gt(cap, 0n) == True{} : Bool}, over: {Nat.is_gt(s, cap) == True{} : Bool}) -> {R.retry_wait(base, attempt, cap, draw, Some{s}) == R.Refused{s, cap} : R.Delay}:
  Retry.retry_refuses_past_cap(R.jitter.draw(R.jitter.step(base, attempt, cap), draw), s, cap, capped, over)

def Retry.retry_wait_server_past_cap(base, attempt, cap, draw, s, capped, over):
  server_past_cap(base, attempt, cap, draw, s, capped, over)
