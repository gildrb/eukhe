# eukhe: the proof of LAW cow_equal_is_same
#
# PROOF: an absent content is the same as itself; an id is equal to itself
# (LA.px.eq_refl).

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def pes.go(+a: Maybe<&2, Nat>) -> {Sb.m.eq(a, a) == True{} : Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Equal.sym(Bool, True{}, Nat.is_eq(x, x), LA.px.eq_refl(x))

def Sandbox.cow_equal_is_same(a):
  pes.go(a)
