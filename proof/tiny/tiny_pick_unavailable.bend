# eukhe: the proof of LAW tiny_pick_unavailable

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny.bend as Tiny
import ./base.bend as LA

def pn.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : LA.tiny.pn.BD(_, Unit, A)
  Unit{}

# a scan with no model of the chain available ends in Unavailable
def pn.go_un(chain: List<&2, Nat>, +up: List<&2, Nat>, hit: Bool, eh: {Tn.up.at(chain, up) == hit : Bool}, none: {Tn.none_up(chain, up) == True{} : Bool}) -> {Tn.pick.go(chain, up, hit) == Tn.Unavailable{} : Tn.Pick}:
  match chain:
    case Nil{}:
      {==}
    case +x <> +rest:
      match hit:
        case True{}:
          +nx = LA.pn.not_t(Tn.elem(up, x), LA.tiny.pn.and_l(Bool.not(Tn.elem(up, x)), Tn.none_up(rest, up), none))
          pn.absurd({Tn.Use{x} == Tn.Unavailable{} : Tn.Pick}, Equal.trans(Bool, True{}, Tn.elem(up, x), False{}, Equal.sym(Bool, Tn.elem(up, x), True{}, eh), nx))
        case False{}:
          pn.go_un(rest, up, Tn.up.at(rest, up), {==}, LA.tiny.pn.and_r(Bool.not(Tn.elem(up, x)), Tn.none_up(rest, up), none))

def pn.tiny_pick_unavailable(+chain: List<&2, Nat>, +up: List<&2, Nat>, none: {Tn.none_up(chain, up) == True{} : Bool}) -> {Tn.pick(chain, up) == Tn.Unavailable{} : Tn.Pick}:
  pn.go_un(chain, up, Tn.up.at(chain, up), {==}, none)

def Tiny.tiny_pick_unavailable(chain, up, none):
  pn.tiny_pick_unavailable(chain, up, none)
