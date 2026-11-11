# eukhe: the proof of LAW search_mem_exact
#
# PROOF: by induction on xs. The empty list holds nothing. In y <> t, x is
# found either at y (is_eq(y, x), so y is x: pre is empty, post is t) or
# in t (the rest's pre and post, y put before pre).

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def mex.BF(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

# False is not True: anything follows
def mex.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : mex.BF(_, A)
  Unit{}

def mex.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      mex.ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      mex.ft({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %mex.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# x is in xs where it says
def mex.Ex(x: Nat, xs: List<&2, Nat>) -> Type:
  &pre: List<&2, Nat> -> &post: List<&2, Nat> -> {xs == List.append(&2, Nat, pre, x <> post) : List<&2, Nat>}

# found at the head
def mex.hit(-y: Nat, -x: Nat, -t: List<&2, Nat>, e: {y == x : Nat}) -> {y <> t == List.append(&2, Nat, Nil{}, x <> t) : List<&2, Nat>}:
  %e : {y <> t == List.append(&2, Nat, Nil{}, _ <> t) : List<&2, Nat>}
  {==}

# found in the rest: y goes before pre
def mex.cons(+y: Nat, -x: Nat, -t: List<&2, Nat>, r: mex.Ex(x, t)) -> mex.Ex(x, y <> t):
  (pre, r1) = r
  (post, pf) = r1
  (y <> pre, (post, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, t, List.append(&2, Nat, pre, x <> post), pf)))

def mex.step(+y: Nat, +x: Nat, q: Bool, eq: {Nat.is_eq(y, x) == q : Bool}, +t: List<&2, Nat>, h: {Bool.or(q, Sr.mem(x, t)) == True{} : Bool}, ih: {Sr.mem(x, t) == True{} : Bool} -> mex.Ex(x, t)) -> mex.Ex(x, y <> t):
  match q:
    case True{}:
      (Nil{}, (t, mex.hit(y, x, t, mex.eq_true(y, x, eq))))
    case False{}:
      mex.cons(y, x, t, ih(h))

def mex.go(+x: Nat, xs: List<&2, Nat>, h: {Sr.mem(x, xs) == True{} : Bool}) -> mex.Ex(x, xs):
  match xs:
    case Nil{}:
      mex.ft(mex.Ex(x, Nil{}), h)
    case +y <> +t:
      mex.step(y, x, Nat.is_eq(y, x), {==}, t, h, hh => mex.go(x, t, hh))

def DocSearch.search_mem_exact(x, xs, h):
  mex.go(x, xs, h)
