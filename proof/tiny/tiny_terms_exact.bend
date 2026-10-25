# eukhe: the proof of LAW tiny_terms_exact
#
# PROOF: both are the same recursion as their specs: by induction on the
# list, `elem` is `sp_in` and `none_up` is `sp_none_up` (whose test of
# each model is `elem`, so `sp_in`).

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny

def tt.elem(xs: List<&2, Nat>, +x: Nat) -> {Tn.elem(xs, x) == Tiny.sp_in(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      %tt.elem(rest, x) : {Bool.or(Nat.is_eq(y, x), Tn.elem(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def tt.none_up(xs: List<&2, Nat>, +up: List<&2, Nat>) -> {Tn.none_up(xs, up) == Tiny.sp_none_up(xs, up) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %tt.elem(up, x) : {Bool.and(Bool.not(Tn.elem(up, x)), Tn.none_up(rest, up)) == Bool.and(Bool.not(_), Tiny.sp_none_up(rest, up)) : Bool}
      %tt.none_up(rest, up) : {Bool.and(Bool.not(Tn.elem(up, x)), Tn.none_up(rest, up)) == Bool.and(Bool.not(Tn.elem(up, x)), _) : Bool}
      {==}

def Tiny.tiny_terms_exact(xs, up, x):
  (tt.elem(xs, x), tt.none_up(xs, up))
