# eukhe: the proof of LAW cow_same_means_equal
#
# PROOF: by cases on both contents: two absent ones are equal; an absent
# and a present one are never the same; two ids the same are equal ids
# (LA.px.eq_true).

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def psm.go(+a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, h: {Sb.m.eq(a, b) == True{} : Bool}) -> {a == b : Maybe<&2, Nat>}:
  match a b:
    case None{} None{}:
      {==}
    case None{} Some{y}:
      LA.px.absurdF({None{} == Some{y} : Maybe<&2, Nat>}, h)
    case Some{x} None{}:
      LA.px.absurdF({Some{x} == None{} : Maybe<&2, Nat>}, h)
    case Some{x} Some{y}:
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, x, y, LA.px.eq_true(x, y, h))

def Sandbox.cow_same_means_equal(a, b, same):
  psm.go(a, b, same)
