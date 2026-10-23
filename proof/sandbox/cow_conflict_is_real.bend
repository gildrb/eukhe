# eukhe: the proof of LAW cow_conflict_is_real

import Base
import ../../bend/sandbox.bend as Sb
import ../../LAWS.bend as Laws
import ./base.bend as LA

def px.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LA.px.absurdF({b == True{} : Bool}, h)

def px.real_go(x: Bool, y: Bool, z: Bool, +p: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, h: {Sb.One.clash(Sb.merge.at(Bool.not(x), Bool.not(y), z, p, c)) == True{} : Bool}) -> {Bool.or(Bool.or(x, y), z) == False{} : Bool}:
  match x y z:
    case True{} _ _:
      LA.px.absurdF({Bool.or(Bool.or(True{}, y), z) == False{} : Bool}, h)
    case False{} True{} _:
      LA.px.absurdF({Bool.or(Bool.or(False{}, True{}), z) == False{} : Bool}, h)
    case False{} False{} True{}:
      LA.px.absurdF({Bool.or(Bool.or(False{}, False{}), True{}) == False{} : Bool}, h)
    case False{} False{} False{}:
      {==}

# a merge that clashes saw both sides change, apart
def px.real(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, h: {Sb.One.clash(Sb.merge1(p, b, c)) == True{} : Bool}) -> {Bool.or(Bool.or(Sb.m.eq(c, b), Sb.m.eq(p, b)), Sb.m.eq(p, c)) == False{} : Bool}:
  px.real_go(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), p, c, h)

def px.cow_conflict_is_real(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, clash: {Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k) == True{} : Bool}) -> {Bool.or(Bool.or(Sb.m.eq(Sb.read(child, k), Sb.read(base, k)), Sb.m.eq(Sb.read(par, k), Sb.read(base, k))), Sb.m.eq(Sb.read(par, k), Sb.read(child, k))) == False{} : Bool}:
  +M = LA.px.mk(par, base, child, k)
  +both = Equal.trans(Bool, Bool.and(Sb.elem(ks, k), Sb.One.clash(M)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k), True{}, LA.px.cl_back(ks, par, base, child, k), clash)
  px.real(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), px.and_r(Sb.elem(ks, k), Sb.One.clash(M), both))

def Laws.cow_conflict_is_real(ks, par, base, child, k, clash):
  px.cow_conflict_is_real(ks, par, base, child, k, clash)
