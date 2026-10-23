# eukhe: the proof of LAW tiny_pick_first

import Base
import ../../bend/tiny.bend as Tn
import ../../LAWS.bend as Laws
import ./base.bend as LA

# a scan past models that are not available reaches the next one
def pn.first(pre: List<&2, Nat>, +m: Nat, +post: List<&2, Nat>, +up: List<&2, Nat>, +before: {Tn.none_up(pre, up) == True{} : Bool}, here: {Tn.elem(up, m) == True{} : Bool}) -> {Tn.pick(List.append(&2, Nat, pre, m <> post), up) == Tn.Use{m} : Tn.Pick}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Tn.elem(up, m), True{}, here) : {Tn.pick.go(m <> post, up, _) == Tn.Use{m} : Tn.Pick}
      {==}
    case +x <> +r:
      +nx = LA.pn.not_t(Tn.elem(up, x), LA.tiny.pn.and_l(Bool.not(Tn.elem(up, x)), Tn.none_up(r, up), before))
      %Equal.sym(Bool, Tn.elem(up, x), False{}, nx) : {Tn.pick.go(x <> List.append(&2, Nat, r, m <> post), up, _) == Tn.Use{m} : Tn.Pick}
      pn.first(r, m, post, up, LA.tiny.pn.and_r(Bool.not(Tn.elem(up, x)), Tn.none_up(r, up), before), here)

def pn.tiny_pick_first(+pre: List<&2, Nat>, +m: Nat, +post: List<&2, Nat>, +up: List<&2, Nat>, before: {Tn.none_up(pre, up) == True{} : Bool}, here: {Tn.elem(up, m) == True{} : Bool}) -> {Tn.pick(List.append(&2, Nat, pre, m <> post), up) == Tn.Use{m} : Tn.Pick}:
  pn.first(pre, m, post, up, before, here)

def Laws.tiny_pick_first(pre, m, post, up, before, here):
  pn.tiny_pick_first(pre, m, post, up, before, here)
