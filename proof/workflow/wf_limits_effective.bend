# eukhe: the proof of LAW wf_limits_effective

import Base
import ../../bend/workflow.bend as W
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

# with a cap 1+x the concurrency is W.capped(b, c, 1+x), b whether c <=
# 1+x: c when it is (at most the cap), else the cap (below c)
def pwl.capped(b: Bool, +c: Nat, +m: Nat, +x: Nat, e: {Nat.is_le(c, 1n+x) == b : Bool}) -> {Workflow.wf_limits_ok(W.Limits{W.capped(b, c, 1n+x), m}, c, m, 1n+x) == True{} : Bool}:
  match b:
    case True{}:
      LA.pw.and_t(Nat.is_eq(m, m), Bool.and(Nat.is_le(c, c), Bool.and(Nat.is_le(c, 1n+x), Bool.or(Nat.is_eq(c, c), Nat.is_eq(c, 1n+x)))), LA.pw.eq_refl(m), LA.pw.and_t(Nat.is_le(c, c), Bool.and(Nat.is_le(c, 1n+x), Bool.or(Nat.is_eq(c, c), Nat.is_eq(c, 1n+x))), LA.pw.le_refl(c), LA.pw.and_t(Nat.is_le(c, 1n+x), Bool.or(Nat.is_eq(c, c), Nat.is_eq(c, 1n+x)), e, LA.pw.or_l(Nat.is_eq(c, c), Nat.is_eq(c, 1n+x), LA.pw.eq_refl(c)))))
    case False{}:
      LA.pw.and_t(Nat.is_eq(m, m), Bool.and(Nat.is_le(1n+x, c), Bool.and(Nat.is_le(1n+x, 1n+x), Bool.or(Nat.is_eq(1n+x, c), Nat.is_eq(1n+x, 1n+x)))), LA.pw.eq_refl(m), LA.pw.and_t(Nat.is_le(1n+x, c), Bool.and(Nat.is_le(1n+x, 1n+x), Bool.or(Nat.is_eq(1n+x, c), Nat.is_eq(1n+x, 1n+x))), LA.pw.le_flip(c, 1n+x, e), LA.pw.and_t(Nat.is_le(1n+x, 1n+x), Bool.or(Nat.is_eq(1n+x, c), Nat.is_eq(1n+x, 1n+x)), LA.pw.le_refl(1n+x), LA.pw.or_r(Nat.is_eq(1n+x, c), Nat.is_eq(1n+x, 1n+x), LA.pw.eq_refl(1n+x)))))

def Workflow.wf_limits_effective(c, m, cap):
  match cap:
    case 0n:
      LA.pw.and_t(Nat.is_eq(m, m), Bool.and(Nat.is_le(c, c), Nat.is_eq(c, c)), LA.pw.eq_refl(m), LA.pw.and_t(Nat.is_le(c, c), Nat.is_eq(c, c), LA.pw.le_refl(c), LA.pw.eq_refl(c)))
    case 1n++x:
      pwl.capped(Nat.is_le(c, 1n+x), c, m, x, {==})
