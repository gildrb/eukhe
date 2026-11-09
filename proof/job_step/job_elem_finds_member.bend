# eukhe: the proof of LAW job_elem_finds_member
# Induction on the items before x: x is equal to itself, and an item
# found further on stays found.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../base/nat.bend as LNat
import ./base.bend as LA

def je.find(xs: List<&2, Nat>, +x: Nat, +ys: List<&2, Nat>) -> {Jb.elem(List.append(&2, Nat, xs, x <> ys), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      %LNat.pf.nat_eq_refl(x) : {Bool.or(_, Jb.elem(ys, x)) == True{} : Bool}
      {==}
    case +y <> rest:
      %Equal.sym(Bool, Jb.elem(List.append(&2, Nat, rest, x <> ys), x), True{}, je.find(rest, x, ys)) : {Bool.or(Nat.is_eq(y, x), _) == True{} : Bool}
      LA.js.or_t(Nat.is_eq(y, x))

def JobStep.job_elem_finds_member(xs, x, ys):
  je.find(xs, x, ys)
