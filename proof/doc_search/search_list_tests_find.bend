# eukhe: the proof of LAW search_list_tests_find
#
# PROOF: by induction on pre. mem: at x itself is_eq(x, x) is True; past
# an item y the test goes on to the rest. nodup: with pre empty, the head
# x is in mid ++ x <> post (the mem half, mid for pre), so not mem is
# False; past an item y the rest already has a duplicate.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def ltf.BF(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

# False is not True: anything follows
def ltf.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ltf.BF(_, A)
  Unit{}

def ltf.eq_refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      ltf.eq_refl(p)

def ltf.or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ltf.ft({Bool.or(False{}, b) == True{} : Bool}, e)

def ltf.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def ltf.and_f(a: Bool, -b: Bool, e: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def ltf.mem(+x: Nat, pre: List<&2, Nat>, +post: List<&2, Nat>) -> {Sr.mem(x, List.append(&2, Nat, pre, x <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      ltf.or_l(Nat.is_eq(x, x), Sr.mem(x, post), ltf.eq_refl(x))
    case +y <> +t:
      ltf.or_r(Nat.is_eq(y, x), Sr.mem(x, List.append(&2, Nat, t, x <> post)), ltf.mem(x, t, post))

def ltf.nodup(+x: Nat, pre: List<&2, Nat>, +mid: List<&2, Nat>, +post: List<&2, Nat>) -> {Sr.nodup(List.append(&2, Nat, pre, x <> List.append(&2, Nat, mid, x <> post))) == False{} : Bool}:
  match pre:
    case Nil{}:
      +rest = List.append(&2, Nat, mid, x <> post)
      %Equal.sym(Bool, Sr.mem(x, rest), True{}, ltf.mem(x, mid, post)) : {Bool.and(Bool.not(_), Sr.nodup(rest)) == False{} : Bool}
      {==}
    case +y <> +t:
      +rest = List.append(&2, Nat, t, x <> List.append(&2, Nat, mid, x <> post))
      ltf.and_f(Bool.not(Sr.mem(y, rest)), Sr.nodup(rest), ltf.nodup(x, t, mid, post))

def DocSearch.search_list_tests_find(x, pre, mid, post):
  (ltf.mem(x, pre, post), ltf.nodup(x, pre, mid, post))
