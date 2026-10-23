# eukhe: the proof of LAW cow_keeps_parent

import Base
import ../../bend/sandbox.bend as Sb
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The merge of one path
# ---------------------

def px.keep_body(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, calm: {Sb.m.eq(c, b) == True{} : Bool}) -> {p == Sb.One.body(Sb.merge1(p, b, c)) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Sb.m.eq(c, b), True{}, calm) : {p == Sb.One.body(Sb.merge.at(Bool.not(_), Bool.not(Sb.m.eq(p, b)), Sb.m.eq(p, c), p, c)) : Maybe<&2, Nat>}
  {==}

# The laws
# --------

def px.cow_keeps_parent(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, listed: {Sb.elem(ks, k) == True{} : Bool}, calm: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == True{} : Bool}) -> {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(par, k) : Maybe<&2, Nat>}:
  %LA.px.read_back(ks, par, base, child, k) : {_ == Sb.read(par, k) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Sb.elem(ks, k), True{}, listed) : {LA.px.sel(_, Sb.One.body(LA.px.mk(par, base, child, k))) == Sb.read(par, k) : Maybe<&2, Nat>}
  %px.keep_body(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), calm) : {_ == Sb.read(par, k) : Maybe<&2, Nat>}
  {==}

def Laws.cow_keeps_parent(ks, par, base, child, k, listed, calm):
  px.cow_keeps_parent(ks, par, base, child, k, listed, calm)
