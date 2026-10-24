# eukhe: the proof of LAW infer_force_after_exact
# A miss on attempt i retries when i < r, which is 1 + i <= r.

import Base
import ../../bend/infer_force.bend as M
import ../../laws/infer_force.bend as InferForce
import ../base/nat.bend as LNat

def ifa.lt_le(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Equal.sym(Bool, Nat.is_le(0n, q), True{}, LNat.pq.le0(q))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ifa.lt_le(p, q)

def ifa.miss(b: Bool) -> {M.after.miss(b) == InferForce.after_spec.miss(b) : M.Next}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def InferForce.infer_force_after_exact(i, r, c):
  match c:
    case True{}:
      {==}
    case False{}:
      %ifa.lt_le(i, r) : {M.after.miss(Nat.is_lt(i, r)) == InferForce.after_spec.miss(_) : M.Next}
      ifa.miss(Nat.is_lt(i, r))
