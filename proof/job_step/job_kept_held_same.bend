# eukhe: the proof of LAW job_kept_held_same
# The check of a held slot asks the same id and the same flag.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job_step.bend as JobStep
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LA

def jh.pick(a: Bool, b: Bool, h: {Bool.and(Bool.and(a, b), True{}) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a b:
    case True{} True{}:
      ({==}, {==})
    case True{} False{}:
      LLogicLogic.pj.absurdF({True{} == True{} : Bool} & {False{} == True{} : Bool}, h)
    case False{} True{}:
      LLogicLogic.pj.absurdF({False{} == True{} : Bool} & {True{} == True{} : Bool}, h)
    case False{} False{}:
      LLogicLogic.pj.absurdF({False{} == True{} : Bool} & {False{} == True{} : Bool}, h)

def jh.beq(r: Bool, q: Bool, h: {Jb.b.eq(r, q) == True{} : Bool}) -> {r == q : Bool}:
  match r q:
    case True{} True{}:
      {==}
    case True{} False{}:
      LLogicLogic.pj.absurdF({True{} == False{} : Bool}, h)
    case False{} True{}:
      LLogicLogic.pj.absurdF({False{} == True{} : Bool}, h)
    case False{} False{}:
      {==}

def jh.fin(+i: Nat, +r: Bool, +h: Nat, +q: Bool, p: {Nat.is_eq(i, h) == True{} : Bool} & {Jb.b.eq(r, q) == True{} : Bool}) -> {Jb.Slot{h, q} == Jb.Slot{i, r} : Jb.Slot}:
  (ei, er) = p
  %LLogicNat.pq.eq_true(i, h, ei) : {Jb.Slot{_, q} == Jb.Slot{i, r} : Jb.Slot}
  %jh.beq(r, q, er) : {Jb.Slot{i, _} == Jb.Slot{i, r} : Jb.Slot}
  {==}

def JobStep.job_kept_held_same(i, r, s, keep, held, ok):
  match s:
    case Jb.Slot{+h, +q}:
      +z = Bool.and(Nat.is_eq(i, h), Jb.b.eq(r, q))
      +e0 = Equal.cong(Bool, Bool, v => Bool.and(Bool.or(Bool.not(v), z), True{}), Jb.elem(keep, i), True{}, held)
      +ok2 = Equal.trans(Bool, Bool.and(z, True{}), Bool.and(Bool.or(Bool.not(Jb.elem(keep, i)), z), True{}), True{}, Equal.sym(Bool, Bool.and(Bool.or(Bool.not(Jb.elem(keep, i)), z), True{}), Bool.and(z, True{}), e0), ok)
      jh.fin(i, r, h, q, jh.pick(Nat.is_eq(i, h), Jb.b.eq(r, q), ok2))
