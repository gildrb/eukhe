# eukhe: the proof of LAW cow_conflict_reported

import Base
import ../../bend/sandbox.bend as Sb
import ../../LAWS.bend as Laws
import ./base.bend as LA

def px.meq_refl(m: Maybe<&2, Nat>) -> {True{} == Sb.m.eq(m, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      LA.px.eq_refl(x)

def px.clash_one(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, moved: {Sb.m.eq(c, b) == False{} : Bool}, also: {Sb.m.eq(p, b) == False{} : Bool}, apart: {Sb.m.eq(p, c) == False{} : Bool}) -> {Sb.One{p, True{}} == Sb.merge1(p, b, c) : Sb.One}:
  %Equal.sym(Bool, Sb.m.eq(c, b), False{}, moved) : {Sb.One{p, True{}} == Sb.merge.at(Bool.not(_), Bool.not(Sb.m.eq(p, b)), Sb.m.eq(p, c), p, c) : Sb.One}
  %Equal.sym(Bool, Sb.m.eq(p, b), False{}, also) : {Sb.One{p, True{}} == Sb.merge.at(True{}, Bool.not(_), Sb.m.eq(p, c), p, c) : Sb.One}
  %Equal.sym(Bool, Sb.m.eq(p, c), False{}, apart) : {Sb.One{p, True{}} == Sb.merge.at(True{}, True{}, _, p, c) : Sb.One}
  {==}

def px.cow_conflict_reported(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, listed: {Sb.elem(ks, k) == True{} : Bool}, moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}, also: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == False{} : Bool}, apart: {Sb.m.eq(Sb.read(par, k), Sb.read(child, k)) == False{} : Bool}) -> {Bool.and(Sb.m.eq(Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k), Sb.read(par, k)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k)) == True{} : Bool}:
  %LA.px.read_back(ks, par, base, child, k) : {Bool.and(Sb.m.eq(_, Sb.read(par, k)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k)) == True{} : Bool}
  %LA.px.cl_back(ks, par, base, child, k) : {Bool.and(Sb.m.eq(LA.px.sel(Sb.elem(ks, k), Sb.One.body(LA.px.mk(par, base, child, k))), Sb.read(par, k)), _) == True{} : Bool}
  %Equal.sym(Bool, Sb.elem(ks, k), True{}, listed) : {Bool.and(Sb.m.eq(LA.px.sel(_, Sb.One.body(LA.px.mk(par, base, child, k))), Sb.read(par, k)), Bool.and(_, Sb.One.clash(LA.px.mk(par, base, child, k)))) == True{} : Bool}
  %px.clash_one(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), moved, also, apart) : {Bool.and(Sb.m.eq(Sb.One.body(_), Sb.read(par, k)), Sb.One.clash(_)) == True{} : Bool}
  %px.meq_refl(Sb.read(par, k)) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def Laws.cow_conflict_reported(ks, par, base, child, k, listed, moved, also, apart):
  px.cow_conflict_reported(ks, par, base, child, k, listed, moved, also, apart)
