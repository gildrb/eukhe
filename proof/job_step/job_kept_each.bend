# eukhe: the proof of LAW job_kept_each
# Induction on both tables at once (same length): "and" regroups; a table
# against itself: each slot has its own id and flag.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../base/nat.bend as LNat
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def jk.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# the check of one slot against itself
def jk.C(+s: Jb.Slot, keep: List<&2, Nat>) -> Bool:
  Bool.or(Bool.not(Jb.elem(keep, Jb.Slot.id(s))), Bool.and(Nat.is_eq(Jb.Slot.id(s), Jb.Slot.id(s)), Jb.b.eq(Jb.Slot.running(s), Jb.Slot.running(s))))

def jk.self_ok(s: Jb.Slot, +keep: List<&2, Nat>) -> {True{} == jk.C(s, keep) : Bool}:
  match s:
    case Jb.Slot{+i, r}:
      match r:
        case True{}:
          %LNat.pf.nat_eq_refl(i) : {True{} == Bool.or(Bool.not(Jb.elem(keep, i)), Bool.and(_, True{})) : Bool}
          Equal.sym(Bool, Bool.or(Bool.not(Jb.elem(keep, i)), True{}), True{}, LA.js.or_t(Bool.not(Jb.elem(keep, i))))
        case False{}:
          %LNat.pf.nat_eq_refl(i) : {True{} == Bool.or(Bool.not(Jb.elem(keep, i)), Bool.and(_, True{})) : Bool}
          Equal.sym(Bool, Bool.or(Bool.not(Jb.elem(keep, i)), True{}), True{}, LA.js.or_t(Bool.not(Jb.elem(keep, i))))

def jk.self(js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.kept(js, js, keep) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case +s <> rest:
      %jk.self_ok(s, keep) : {Bool.and(_, Jb.kept(rest, rest, keep)) == True{} : Bool}
      jk.self(rest, keep)

def jk.app(js: List<&2, Jb.Slot>, ks: List<&2, Jb.Slot>, +js2: List<&2, Jb.Slot>, +ks2: List<&2, Jb.Slot>, +keep: List<&2, Nat>, same: {List.length(&2, Jb.Slot, js) == List.length(&2, Jb.Slot, ks) : Nat}) -> {Jb.kept(List.append(&2, Jb.Slot, js, js2), List.append(&2, Jb.Slot, ks, ks2), keep) == Bool.and(Jb.kept(js, ks, keep), Jb.kept(js2, ks2, keep)) : Bool}:
  match js ks:
    case Nil{} Nil{}:
      {==}
    case Nil{} k <> kr:
      LLogicLogic.pf.succ_ne_zero({Jb.kept(js2, List.append(&2, Jb.Slot, k <> kr, ks2), keep) == Bool.and(Jb.kept(Nil{}, k <> kr, keep), Jb.kept(js2, ks2, keep)) : Bool}, List.length(&2, Jb.Slot, kr), Equal.sym(Nat, 0n, 1n+List.length(&2, Jb.Slot, kr), same))
    case j <> jr Nil{}:
      LLogicLogic.pf.succ_ne_zero({Jb.kept(List.append(&2, Jb.Slot, j <> jr, js2), ks2, keep) == Bool.and(Jb.kept(j <> jr, Nil{}, keep), Jb.kept(js2, ks2, keep)) : Bool}, List.length(&2, Jb.Slot, jr), same)
    case +j <> jr +k <> kr:
      +c = Bool.or(Bool.not(Jb.elem(keep, Jb.Slot.id(j))), Bool.and(Nat.is_eq(Jb.Slot.id(j), Jb.Slot.id(k)), Jb.b.eq(Jb.Slot.running(j), Jb.Slot.running(k))))
      +s2 = Equal.cong(Nat, Nat, n => jk.pred(n), 1n+List.length(&2, Jb.Slot, jr), 1n+List.length(&2, Jb.Slot, kr), same)
      %Equal.sym(Bool, Jb.kept(List.append(&2, Jb.Slot, jr, js2), List.append(&2, Jb.Slot, kr, ks2), keep), Bool.and(Jb.kept(jr, kr, keep), Jb.kept(js2, ks2, keep)), jk.app(jr, kr, js2, ks2, keep, s2)) : {Bool.and(c, _) == Bool.and(Bool.and(c, Jb.kept(jr, kr, keep)), Jb.kept(js2, ks2, keep)) : Bool}
      LA.js.and_assoc(c, Jb.kept(jr, kr, keep), Jb.kept(js2, ks2, keep))

def JobStep.job_kept_each(js, ks, js2, ks2, keep, s, same):
  (jk.app(js, ks, js2, ks2, keep, same), ({==}, ({==}, jk.self(js, keep))))
