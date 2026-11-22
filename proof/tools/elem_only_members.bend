# eukhe: the proof of LAW elem_only_members
#
# PROOF: by induction on xs. The empty list has no element. y then rest:
# when y is c, c stands first (nothing before it, rest after it); else c
# is an element of rest (the or's second test), which holds it after some
# entries (induction), so y then those entries come before c.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

# rest holds c after pre: y then rest holds it after y then pre
def eo.cons(+y: Nat, +rest: List<&2, Nat>, -c: Nat, s: Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {rest == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>}>>) -> Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {y <> rest == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>}>>:
  match s:
    case (+pre, t):
      match t:
        case (+post, e):
          (y <> pre, (post, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, rest, List.append(&2, Nat, pre, c <> post), e)))

# the head test b of y then rest: y is c, or rest holds c (ih)
def eo.head(b: Bool, +y: Nat, +rest: List<&2, Nat>, +c: Nat, eb: {Nat.is_eq(y, c) == b : Bool}, h: {Bool.or(b, Tl.elem(rest, c)) == True{} : Bool}, ih: {Tl.elem(rest, c) == True{} : Bool} -> Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {rest == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>}>>) -> Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {y <> rest == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>}>>:
  match b:
    case True{}:
      (Nil{}, (rest, Equal.cong(Nat, List<&2, Nat>, z => z <> rest, y, c, LA.shell.ps.eq_of_is_eq(y, c, eb))))
    case False{}:
      eo.cons(y, rest, c, ih(h))

def eo.go(xs: List<&2, Nat>, +c: Nat, has: {Tl.elem(xs, c) == True{} : Bool}) -> Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {xs == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>}>>:
  match xs:
    case Nil{}:
      LA.shell.ps.absurdF(Sigma<&1, &1, List<&2, Nat>, pre => Sigma<&1, &1, List<&2, Nat>, post => {Nil{} == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>}>>, has)
    case +y <> +rest:
      eo.head(Nat.is_eq(y, c), y, rest, c, {==}, has, k => eo.go(rest, c, k))

def Tools.elem_only_members(xs, c, has):
  eo.go(xs, c, has)
