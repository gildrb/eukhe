# eukhe: the proof of LAW tag_line_outside
#
# PROOF: line 0 is no line by `is_line`'s first arm; for n = 1 + m past
# the end, index m of t is past its last item (|t| < 1 + m), so the lookup
# finds nothing (by induction on t).

import Base
import ../../bend/doc_tags.bend as Dt
import ../../laws/doc_tags.bend as DocTags

def tlo.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def tlo.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : tlo.BT(_, G)
  Unit{}

# no index 0 of a list whose length is below 1
def tlo.zero(-x: Nat, r: List<&2, Nat>, h: {Nat.is_lt(1n+List.length(&2, Nat, r), 1n) == True{} : Bool}) -> {List.get(&2, Nat, x <> r, 0n) == None{} : Maybe<&2, Nat>}:
  match r:
    case Nil{}:
      tlo.ft({List.get(&2, Nat, [x], 0n) == None{} : Maybe<&2, Nat>}, h)
    case y <> u:
      tlo.ft({List.get(&2, Nat, x <> y <> u, 0n) == None{} : Maybe<&2, Nat>}, h)

# index m of t is past its end when |t| < 1 + m
def tlo.none(t: List<&2, Nat>, m: Nat, h: {Nat.is_lt(List.length(&2, Nat, t), 1n+m) == True{} : Bool}) -> {List.get(&2, Nat, t, m) == None{} : Maybe<&2, Nat>}:
  match t m:
    case Nil{} m:
      {==}
    case x <> r 0n:
      tlo.zero(x, r, h)
    case x <> r 1n+p:
      tlo.none(r, p, h)

def tlo.at(+t: List<&2, Nat>, n: Nat, +x: Nat, h: {Nat.is_lt(List.length(&2, Nat, t), n) == True{} : Bool}) -> {(Dt.is_line(t, 0n, x), Dt.is_line(t, n, x)) == (False{}, False{}) : Bool & Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, t, m), None{}, tlo.none(t, m, h)) : {(False{}, Maybe.default(&2, Bool, Maybe.bind(&2, Nat, Bool, _, y => Some{Nat.is_eq(y, x)}), False{})) == (False{}, False{}) : Bool & Bool}
      {==}

def DocTags.tag_line_outside(t, n, x, h):
  tlo.at(t, n, x, h)
