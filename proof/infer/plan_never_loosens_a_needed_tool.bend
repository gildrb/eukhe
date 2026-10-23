# eukhe: the proof of LAW plan_never_loosens_a_needed_tool

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_eq.bend as LNatIsEq
import ./base.bend as LA

def w2.of_none(m: Maybe<&2, Nat>, +L: List<&2, If.Tool>, +ls: List<&2, Nat>, f: {If.plan.of(m, L) == If.Fits{ls} : If.Plan}) -> {m == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      LBoolMisc.pq.absurd({Some{i} == None{} : Maybe<&2, Nat>}, Equal.cong(If.Plan, Bool, LA.w2.over, If.Over{i}, If.Fits{ls}, f))

# is_eq(a, i) true, a not needed, i needed: impossible
def w2.eq_ne(+a: Nat, +i: Nat, h: {Nat.is_eq(a, i) == True{} : Bool}, +need: List<&2, Nat>, en: {If.elem(need, a) == False{} : Bool}, n: {If.elem(need, i) == True{} : Bool}) -> Empty:
  +na = LA.w2.elem_at(need, a, i, LNatIsEq.pq.eq_true(a, i, h), n)
  LBoolMisc.pq.absurd(Empty, Equal.trans(Bool, True{}, If.elem(need, a), False{}, Equal.sym(Bool, If.elem(need, a), True{}, na), en))

def w2.or_f(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case False{}:
      eb
    case True{}:
      LBoolMisc.pq.absurd({Bool.or(True{}, b) == False{} : Bool}, ea)

def w2.ne_of(+a: Nat, +i: Nat, +need: List<&2, Nat>, en: {If.elem(need, a) == False{} : Bool}, n: {If.elem(need, i) == True{} : Bool}, e: Bool, ee: {Nat.is_eq(a, i) == e : Bool}) -> {Nat.is_eq(a, i) == False{} : Bool}:
  match e:
    case False{}:
      ee
    case True{}:
      Empty.absurd({Nat.is_eq(a, i) == False{} : Bool}, w2.eq_ne(a, i, ee, need, en, n))

# no tool of ls needs a strict schema: no needed id is among ids(ls)
def w2.none_go(+ls: List<&2, If.Tool>, +need: List<&2, Nat>, hit: Bool, eh: {If.needs.at(ls, need) == hit : Bool}, z: {If.needs.go(ls, need, hit) == None{} : Maybe<&2, Nat>}, +i: Nat, +n: {If.elem(need, i) == True{} : Bool}) -> {If.elem(If.ids(ls), i) == False{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case t <> rest:
      match hit:
        case True{}:
          LA.w2.mt({If.elem(If.ids(t <> rest), i) == False{} : Bool}, If.Tool.id(t), z)
        case False{}:
          +a = If.Tool.id(t)
          w2.or_f(Nat.is_eq(a, i), If.elem(If.ids(rest), i), w2.ne_of(a, i, need, eh, n, Nat.is_eq(a, i), {==}), w2.none_go(rest, need, If.needs.at(rest, need), {==}, z, i, n))

def Infer.plan_never_loosens_a_needed_tool(cap, ts, need, ls, i, f, n):
  +L = Pair.snd(List<&2, If.Tool>, List<&2, If.Tool>, If.strict.of(cap, ts))
  +M = If.needs.go(L, need, If.needs.at(L, need))
  %Equal.sym(List<&2, Nat>, ls, If.ids(L), LA.w2.of_fits(M, L, ls, f)) : {If.elem(_, i) == False{} : Bool}
  w2.none_go(L, need, If.needs.at(L, need), {==}, w2.of_none(M, L, ls, f), i, n)
