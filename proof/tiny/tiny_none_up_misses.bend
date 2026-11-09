# eukhe: the proof of LAW tiny_none_up_misses
#
# PROOF: by induction on the models before x: `none_up` of a list is the
# `and` of "not available" over its models, so each conjunct holds; at x
# it says x is not available.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny
import ./base.bend as LA

def tnm.go(pre: List<&2, Nat>, +x: Nat, +post: List<&2, Nat>, +up: List<&2, Nat>, none: {Tn.none_up(List.append(&2, Nat, pre, x <> post), up) == True{} : Bool}) -> {Tn.elem(up, x) == False{} : Bool}:
  match pre:
    case Nil{}:
      LA.pn.not_t(Tn.elem(up, x), LA.tiny.pn.and_l(Bool.not(Tn.elem(up, x)), Tn.none_up(post, up), none))
    case +y <> +rest:
      tnm.go(rest, x, post, up, LA.tiny.pn.and_r(Bool.not(Tn.elem(up, y)), Tn.none_up(List.append(&2, Nat, rest, x <> post), up), none))

def Tiny.tiny_none_up_misses(pre, x, post, up, none):
  tnm.go(pre, x, post, up, none)
