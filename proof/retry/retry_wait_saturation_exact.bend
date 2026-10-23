# eukhe: the proof of LAW retry_wait_saturation_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base.bend as LA

# under a positive cap the wait is the server pick of s > cap
def rx.capped(+jitter: Nat, +s: Nat, +cap: Nat, capped: {Nat.is_gt(cap, 0n) == True{} : Bool}) -> {R.wait.server(Nat.is_gt(s, cap), jitter, s, cap) == R.wait(jitter, Some{s}, cap) : R.Delay}:
  %Equal.sym(Bool, Nat.is_gt(cap, 0n), True{}, capped) : {R.wait.server(Nat.is_gt(s, cap), jitter, s, cap) == R.wait.server(Bool.and(_, Nat.is_gt(s, cap)), jitter, s, cap) : R.Delay}
  {==}

def rx.sat_go(over: Bool, +jitter: Nat, +s: Nat, +cap: Nat, +c: Nat, +eo: {Nat.is_gt(s, cap) == over : Bool}, above: {Nat.is_gt(c, cap) == True{} : Bool}) -> {Retry.rs.held(R.wait.server(Nat.is_gt(Nat.min(s, c), cap), jitter, Nat.min(s, c), cap)) == Retry.rs.held(R.wait.server(over, jitter, s, cap)) : Maybe<&2, Nat>}:
  match over:
    case True{}:
      %Equal.sym(Bool, Nat.is_gt(Nat.min(s, c), cap), True{}, LA.rx.gt_min(s, c, cap, eo, above)) : {Retry.rs.held(R.wait.server(_, jitter, Nat.min(s, c), cap)) == None{} : Maybe<&2, Nat>}
      {==}
    case False{}:
      +le = LA.rx.le_gt(s, cap, c, LA.rx.le_of_not_gt(Nat.cmp(s, cap), eo), above)
      %Equal.sym(Nat, Nat.min(s, c), s, LA.rx.min_l(s, c, le)) : {Retry.rs.held(R.wait.server(Nat.is_gt(_, cap), jitter, _, cap)) == Some{Nat.max(jitter, s)} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_gt(s, cap), False{}, eo) : {Retry.rs.held(R.wait.server(_, jitter, s, cap)) == Some{Nat.max(jitter, s)} : Maybe<&2, Nat>}
      {==}

def wait_saturation_exact(+jitter: Nat, +s: Nat, +cap: Nat, +c: Nat, +capped: {Nat.is_gt(cap, 0n) == True{} : Bool}, above: {Nat.is_gt(c, cap) == True{} : Bool}) -> {Retry.rs.held(R.wait(jitter, Some{Nat.min(s, c)}, cap)) == Retry.rs.held(R.wait(jitter, Some{s}, cap)) : Maybe<&2, Nat>}:
  %rx.capped(jitter, Nat.min(s, c), cap, capped) : {Retry.rs.held(_) == Retry.rs.held(R.wait(jitter, Some{s}, cap)) : Maybe<&2, Nat>}
  %rx.capped(jitter, s, cap, capped) : {Retry.rs.held(R.wait.server(Nat.is_gt(Nat.min(s, c), cap), jitter, Nat.min(s, c), cap)) == Retry.rs.held(_) : Maybe<&2, Nat>}
  rx.sat_go(Nat.is_gt(s, cap), jitter, s, cap, c, {==}, above)

def Retry.retry_wait_saturation_exact(jitter, s, cap, c, capped, above):
  wait_saturation_exact(jitter, s, cap, c, capped, above)
