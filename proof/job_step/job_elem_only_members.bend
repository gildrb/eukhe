# eukhe: the proof of LAW job_elem_only_members
# Induction on the list: the head is x (then x heads it), or x is found
# in the tail (then x stands in the tail).

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LA

def jo.G(ys: List<&2, Nat>, x: Nat) -> Type:
  Sigma<&1, &1, List<&2, Nat>, xs => Sigma<&1, &1, List<&2, Nat>, zs => {ys == List.append(&2, Nat, xs, x <> zs) : List<&2, Nat>}>>

# x stands in the tail, so in the list
def jo.cons(+y: Nat, -rest: List<&2, Nat>, -x: Nat, g: jo.G(rest, x)) -> jo.G(y <> rest, x):
  (+xs, (+zs, e)) = g
  (y <> xs, (zs, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, rest, List.append(&2, Nat, xs, x <> zs), e)))

def jo.head(b: Bool, +y: Nat, +x: Nat, +rest: List<&2, Nat>, eb: {Nat.is_eq(y, x) == b : Bool}, found: {Bool.or(Nat.is_eq(y, x), Jb.elem(rest, x)) == True{} : Bool}, ih: {Jb.elem(rest, x) == True{} : Bool} -> jo.G(rest, x)) -> jo.G(y <> rest, x):
  match b:
    case True{}:
      (Nil{}, (rest, Equal.cong(Nat, List<&2, Nat>, z => z <> rest, y, x, LLogicNat.pq.eq_true(y, x, eb))))
    case False{}:
      +er = Equal.trans(Bool, Jb.elem(rest, x), Bool.or(Nat.is_eq(y, x), Jb.elem(rest, x)), True{}, Equal.sym(Bool, Bool.or(Nat.is_eq(y, x), Jb.elem(rest, x)), Jb.elem(rest, x), Equal.cong(Bool, Bool, v => Bool.or(v, Jb.elem(rest, x)), Nat.is_eq(y, x), False{}, eb)), found)
      jo.cons(y, rest, x, ih(er))

def jo.go(ys: List<&2, Nat>, +x: Nat, found: {Jb.elem(ys, x) == True{} : Bool}) -> jo.G(ys, x):
  match ys:
    case Nil{}:
      LLogicLogic.pj.absurdF(jo.G(Nil{}, x), found)
    case +y <> +rest:
      jo.head(Nat.is_eq(y, x), y, x, rest, {==}, found, h => jo.go(rest, x, h))

def JobStep.job_elem_only_members(ys, x, found):
  jo.go(ys, x, found)
