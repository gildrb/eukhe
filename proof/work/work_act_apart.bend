# eukhe: the proof of LAW work_act_apart
# Two acts' numbers are equal exactly when their calls and results are
# (LAWork.wt.res); here one of the two is the same on both sides.

import Base
import ../../laws/work.bend as Work
import ../../bend/progress.bend as Pr
import ./base.bend as LWork

def wa.meq_refl(m: Maybe<&2, Nat>) -> {Pr.meq(m, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      LWork.wt.refl(c)

def wa.result(+m: Maybe<&2, Nat>, +r: Nat, +x: Nat) -> {Nat.is_eq(Pr.act(m, r), Pr.act(m, x)) == Nat.is_eq(r, x) : Bool}:
  Equal.trans(Bool, Nat.is_eq(Pr.act(m, r), Pr.act(m, x)), Bool.and(Pr.meq(m, m), Nat.is_eq(r, x)), Nat.is_eq(r, x), LWork.wt.res(m, m, r, x), Equal.cong(Bool, Bool, v => Bool.and(v, Nat.is_eq(r, x)), Pr.meq(m, m), True{}, wa.meq_refl(m)))

def wa.call(+c: Nat, +d: Nat, +r: Nat) -> {Nat.is_eq(Pr.act(Some{c}, r), Pr.act(Some{d}, r)) == Nat.is_eq(c, d) : Bool}:
  +e = Nat.is_eq(c, d)
  Equal.trans(Bool, Nat.is_eq(Pr.act(Some{c}, r), Pr.act(Some{d}, r)), Bool.and(e, True{}), e, Equal.trans(Bool, Nat.is_eq(Pr.act(Some{c}, r), Pr.act(Some{d}, r)), Bool.and(e, Nat.is_eq(r, r)), Bool.and(e, True{}), LWork.wt.res(Some{c}, Some{d}, r, r), Equal.cong(Bool, Bool, v => Bool.and(e, v), Nat.is_eq(r, r), True{}, LWork.wt.refl(r))), LWork.wt.and_true(e))

def Work.work_act_apart(m, c, d, r, x):
  (wa.result(m, r, x), wa.call(c, d, r), LWork.wt.res(None{}, Some{c}, r, r))
