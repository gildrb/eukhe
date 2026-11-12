# eukhe: the proof of LAW retry_wait_server_within
# The wait of a retry is the wait of its jitter J (retry_wait unfolds to
# wait); with no server wait it is After{J}, so ms is J (rv.ms). A server
# wait within the cap, or under a cap of 0, is not over it (rv.within), so
# the wait is the longer of J and the server's.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/logic/logic.bend as LLogicLogic

# the ms of a wait (0 for a refusal)
def rv.ms(w: R.Delay) -> Nat:
  match w:
    case R.After{m}:
      m
    case R.Refused{s, c}:
      0n

def rv.not_gt(c: Cmp, e: {Cmp.is_le(c) == True{} : Bool}) -> {Cmp.is_gt(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      LLogicLogic.rp.absurdF({True{} == False{} : Bool}, e)

# a server wait within the cap, or under no cap, is not over it
def rv.within(c: Nat, +s: Nat, within: {Bool.or(Nat.is_eq(c, 0n), Nat.is_le(s, c)) == True{} : Bool}) -> {Bool.and(Nat.is_gt(c, 0n), Nat.is_gt(s, c)) == False{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      rv.not_gt(Nat.cmp(s, 1n+cp), within)

def rv.after(over: Bool, +j: Nat, +s: Nat, +c: Nat, e: {over == False{} : Bool}) -> {R.wait.server(over, j, s, c) == R.After{Nat.max(j, s)} : R.Delay}:
  match over:
    case True{}:
      LLogicLogic.rp.absurdT({R.wait.server(True{}, j, s, c) == R.After{Nat.max(j, s)} : R.Delay}, e)
    case False{}:
      {==}

def server_within(+base: Nat, +attempt: Nat, +cap: Nat, +draw: Nat, +s: Nat, +ms: Nat, within: {Bool.or(Nat.is_eq(cap, 0n), Nat.is_le(s, cap)) == True{} : Bool}, own: {R.retry_wait(base, attempt, cap, draw, None{}) == R.After{ms} : R.Delay}) -> {R.retry_wait(base, attempt, cap, draw, Some{s}) == R.After{Nat.max(ms, s)} : R.Delay}:
  +J = R.jitter.draw(R.jitter.step(base, attempt, cap), draw)
  +ej = Equal.cong(R.Delay, Nat, w => rv.ms(w), R.After{J}, R.After{ms}, own)
  %ej : {R.retry_wait(base, attempt, cap, draw, Some{s}) == R.After{Nat.max(_, s)} : R.Delay}
  rv.after(Bool.and(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap)), J, s, cap, rv.within(cap, s, within))

def Retry.retry_wait_server_within(base, attempt, cap, draw, s, ms, within, own):
  server_within(base, attempt, cap, draw, s, ms, within, own)
