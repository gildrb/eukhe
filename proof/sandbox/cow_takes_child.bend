# eukhe: the proof of LAW cow_takes_child

import Base
import ../../bend/sandbox.bend as Sb
import ../../LAWS.bend as Laws
import ./base.bend as LA

def px.take_body(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, moved: {Sb.m.eq(c, b) == False{} : Bool}, still: {Sb.m.eq(p, b) == True{} : Bool}) -> {c == Sb.One.body(Sb.merge1(p, b, c)) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Sb.m.eq(c, b), False{}, moved) : {c == Sb.One.body(Sb.merge.at(Bool.not(_), Bool.not(Sb.m.eq(p, b)), Sb.m.eq(p, c), p, c)) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Sb.m.eq(p, b), True{}, still) : {c == Sb.One.body(Sb.merge.at(True{}, Bool.not(_), Sb.m.eq(p, c), p, c)) : Maybe<&2, Nat>}
  {==}

def px.cow_takes_child(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, listed: {Sb.elem(ks, k) == True{} : Bool}, moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}, still: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == True{} : Bool}) -> {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(child, k) : Maybe<&2, Nat>}:
  %LA.px.read_back(ks, par, base, child, k) : {_ == Sb.read(child, k) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Sb.elem(ks, k), True{}, listed) : {LA.px.sel(_, Sb.One.body(LA.px.mk(par, base, child, k))) == Sb.read(child, k) : Maybe<&2, Nat>}
  %px.take_body(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), moved, still) : {_ == Sb.read(child, k) : Maybe<&2, Nat>}
  {==}

def Laws.cow_takes_child(ks, par, base, child, k, listed, moved, still):
  px.cow_takes_child(ks, par, base, child, k, listed, moved, still)
