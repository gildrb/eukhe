# eukhe: the proof of LAW grep_opened_class
#
# PROOF: with no match left the class computes; with one left, a file of
# no match is NoMatch and its cut test (min(p, rem) < 0) is False; a file
# of matches is classed by its page test, and min(p, rem) < h exactly
# when min(h, min(p, rem)) < h (keeping all h is no cut).

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def oc.lt_zero(m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      {==}

# keeping min(h, m) of h cuts exactly when m < h
def oc.lt_min(h: Nat, m: Nat) -> {Nat.is_lt(m, h) == Nat.is_lt(Nat.min(h, m), h) : Bool}:
  match h m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+g 0n:
      {==}
    case 1n+g 1n+q:
      oc.lt_min(g, q)

def oc.page(b: Bool) -> {Sr.page.cls(b) == DocSearch.ds_on_page(b) : Sr.Class}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def oc.none(+i: Nat, big: Bool, +p: Nat, s: Nat, k: Nat, +r: Nat, n: Nat) -> {Sr.out(Sr.Ent{i, Sr.Opened{0n, big}}, p, s, k, 1n+r, n) == Sr.Out{i, Sr.NoMatch{}, False{}, big} : Sr.Out}:
  %oc.lt_zero(Nat.min(p, 1n+r)) : {Sr.Out{i, Sr.NoMatch{}, Nat.is_lt(Nat.min(p, 1n+r), 0n), big} == Sr.Out{i, Sr.NoMatch{}, _, big} : Sr.Out}
  {==}

def oc.some(+i: Nat, +g: Nat, big: Bool, +p: Nat, +s: Nat, +k: Nat, +r: Nat, +n: Nat) -> {Sr.out(Sr.Ent{i, Sr.Opened{1n+g, big}}, p, s, k, 1n+r, n) == Sr.Out{i, DocSearch.ds_on_page(Bool.and(Nat.is_le(s, n), Nat.is_lt(n, Nat.add(s, k)))), Nat.is_lt(Sr.kept(Sr.Ent{i, Sr.Opened{1n+g, big}}, p, 1n+r), 1n+g), big} : Sr.Out}:
  +b = Bool.and(Nat.is_le(s, n), Nat.is_lt(n, Nat.add(s, k)))
  +m = Nat.min(p, 1n+r)
  %oc.page(b) : {Sr.Out{i, Sr.page.cls(b), Nat.is_lt(m, 1n+g), big} == Sr.Out{i, _, Nat.is_lt(Nat.min(1n+g, m), 1n+g), big} : Sr.Out}
  %oc.lt_min(1n+g, m) : {Sr.Out{i, Sr.page.cls(b), Nat.is_lt(m, 1n+g), big} == Sr.Out{i, Sr.page.cls(b), _, big} : Sr.Out}
  {==}

def DocSearch.grep_opened_class(i, h, g, big, p, s, k, r, n):
  ({==}, (oc.none(i, big, p, s, k, r, n), oc.some(i, g, big, p, s, k, r, n)))
