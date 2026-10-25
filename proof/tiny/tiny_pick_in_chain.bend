# eukhe: the proof of LAW tiny_pick_in_chain

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny
import ./base.bend as LA

def tiny.pn.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pn.or_r(x: Bool, +a: Bool, h: {a == True{} : Bool}) -> {Bool.or(x, a) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

# Picks
# -----

def pn.PD(p: Tn.Pick, u: Type, n: Type) -> Type:
  match p:
    case Tn.Use{m}:
      u
    case Tn.Unavailable{}:
      n

def pn.un_use(-A: Type, -m: Nat, e: {Tn.Unavailable{} == Tn.Use{m} : Tn.Pick}) -> A:
  %e : pn.PD(_, A, Unit)
  Unit{}

def pn.use_m(p: Tn.Pick) -> Nat:
  match p:
    case Tn.Use{m}:
      m
    case Tn.Unavailable{}:
      0n

def pn.use_inj(-a: Nat, -b: Nat, e: {Tn.Use{a} == Tn.Use{b} : Tn.Pick}) -> {a == b : Nat}:
  Equal.cong(Tn.Pick, Nat, p => pn.use_m(p), Tn.Use{a}, Tn.Use{b}, e)

# a scan that uses m found it in the chain and available
def pn.go_in(chain: List<&2, Nat>, +up: List<&2, Nat>, +m: Nat, hit: Bool, eh: {Tn.up.at(chain, up) == hit : Bool}, used: {Tn.pick.go(chain, up, hit) == Tn.Use{m} : Tn.Pick}) -> {Bool.and(Tn.elem(chain, m), Tn.elem(up, m)) == True{} : Bool}:
  match chain:
    case Nil{}:
      pn.un_use({Bool.and(False{}, Tn.elem(up, m)) == True{} : Bool}, m, used)
    case +h <> +rest:
      match hit:
        case True{}:
          %pn.use_inj(h, m, used) : {Bool.and(Tn.elem(h <> rest, _), Tn.elem(up, _)) == True{} : Bool}
          %LA.pn.eq_refl(h) : {Bool.and(Bool.or(_, Tn.elem(rest, h)), Tn.elem(up, h)) == True{} : Bool}
          eh
        case False{}:
          +ih = pn.go_in(rest, up, m, Tn.up.at(rest, up), {==}, used)
          +hr = LA.tiny.pn.and_l(Tn.elem(rest, m), Tn.elem(up, m), ih)
          +hu = LA.tiny.pn.and_r(Tn.elem(rest, m), Tn.elem(up, m), ih)
          tiny.pn.and_t(Bool.or(Nat.is_eq(h, m), Tn.elem(rest, m)), Tn.elem(up, m), pn.or_r(Nat.is_eq(h, m), Tn.elem(rest, m), hr), hu)

# The laws
# --------

def pn.tiny_pick_in_chain(+chain: List<&2, Nat>, +up: List<&2, Nat>, +m: Nat, used: {Tn.pick(chain, up) == Tn.Use{m} : Tn.Pick}) -> {Bool.and(Tn.elem(chain, m), Tn.elem(up, m)) == True{} : Bool}:
  pn.go_in(chain, up, m, Tn.up.at(chain, up), {==}, used)

# (S9) Local tiny models

def Tiny.tiny_pick_in_chain(chain, up, m, used):
  pn.tiny_pick_in_chain(chain, up, m, used)
