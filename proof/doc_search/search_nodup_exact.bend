# eukhe: the proof of LAW search_nodup_exact
#
# PROOF: by induction on xs. The empty list has no duplicate. y <> t has
# one either because y is in t (search_mem_exact splits t as mid ++ y <>
# post: x is y, pre is empty) or because t has one (y put before pre).

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def ndx.BT(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

# True is not False: anything follows
def ndx.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ndx.BT(_, A)
  Unit{}

# some x is in xs twice, where it says
def ndx.Ex(xs: List<&2, Nat>) -> Type:
  &x: Nat -> &pre: List<&2, Nat> -> &mid: List<&2, Nat> -> &post: List<&2, Nat> -> {xs == List.append(&2, Nat, pre, x <> List.append(&2, Nat, mid, x <> post)) : List<&2, Nat>}

# y again in t
def ndx.dup(+y: Nat, -t: List<&2, Nat>, r: &mid: List<&2, Nat> -> &post: List<&2, Nat> -> {t == List.append(&2, Nat, mid, y <> post) : List<&2, Nat>}) -> ndx.Ex(y <> t):
  (mid, r1) = r
  (post, pf) = r1
  (y, (Nil{}, (mid, (post, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, t, List.append(&2, Nat, mid, y <> post), pf)))))

# a duplicate in t: y goes before pre
def ndx.cons(+y: Nat, -t: List<&2, Nat>, r: ndx.Ex(t)) -> ndx.Ex(y <> t):
  (x, r1) = r
  (pre, r2) = r1
  (mid, r3) = r2
  (post, pf) = r3
  (x, (y <> pre, (mid, (post, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, t, List.append(&2, Nat, pre, x <> List.append(&2, Nat, mid, x <> post)), pf)))))

def ndx.step(+y: Nat, +t: List<&2, Nat>, q: Bool, eq: {Sr.mem(y, t) == q : Bool}, h: {Bool.and(Bool.not(q), Sr.nodup(t)) == False{} : Bool}, ih: {Sr.nodup(t) == False{} : Bool} -> ndx.Ex(t)) -> ndx.Ex(y <> t):
  match q:
    case True{}:
      ndx.dup(y, t, DocSearch.search_mem_exact(y, t, eq))
    case False{}:
      ndx.cons(y, t, ih(h))

def ndx.go(xs: List<&2, Nat>, h: {Sr.nodup(xs) == False{} : Bool}) -> ndx.Ex(xs):
  match xs:
    case Nil{}:
      ndx.tf(ndx.Ex(Nil{}), h)
    case +y <> +t:
      ndx.step(y, t, Sr.mem(y, t), {==}, h, hh => ndx.go(t, hh))

def DocSearch.search_nodup_exact(xs, h):
  ndx.go(xs, h)
