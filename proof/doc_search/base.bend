# eukhe: lemmas the proofs of area doc_search share

import Base
import ../../bend/doc_search.bend as Sr

def documents.ps.MD(m: Maybe<&2, Nat>, t: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      t

def documents.ps.none_some(-A: Type, -c: Nat, e: {None{} == Some{c} : Maybe<&2, Nat>}) -> A:
  %e : documents.ps.MD(_, A)
  Unit{}

def ps.some_inj(-a: Nat, -b: Nat, e: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), Some{a}, Some{b}, e)

# Pages
# -----

def ps.take_drop(xs: List<&2, Nat>, k: Nat) -> {List.append(&2, Nat, List.take(&2, Nat, xs, k), List.drop(&2, Nat, xs, k)) == xs : List<&2, Nat>}:
  match xs k:
    case Nil{} k:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      %ps.take_drop(t, p) : {h <> List.append(&2, Nat, List.take(&2, Nat, t, p), List.drop(&2, Nat, t, p)) == h <> _ : List<&2, Nat>}
      {==}

def ps.drop_drop(xs: List<&2, Nat>, s: Nat, +k: Nat) -> {List.drop(&2, Nat, List.drop(&2, Nat, xs, s), k) == List.drop(&2, Nat, xs, Nat.add(s, k)) : List<&2, Nat>}:
  match xs s:
    case Nil{} s:
      match k:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      ps.drop_drop(t, p, k)

def ps.put_c(after: List<&2, Nat>, -c0: Nat, -c: Nat, h: {Sr.next.put(after, c0) == Some{c} : Maybe<&2, Nat>}) -> {c0 == c : Nat}:
  match after:
    case Nil{}:
      documents.ps.none_some({c0 == c : Nat}, c, h)
    case x <> t:
      ps.some_inj(c0, c, h)

# the continuation is S + K
def ps.next_c(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> {Nat.add(s, k) == c : Nat}:
  match k:
    case 0n:
      documents.ps.none_some({Nat.add(s, 0n) == c : Nat}, c, h)
    case 1n+j:
      ps.put_c(List.drop(&2, Nat, ps, Nat.add(s, 1n+j)), Nat.add(s, 1n+j), c, h)

# the page at S + K and what follows it are the list after S
def ps.contig(+ps: List<&2, Nat>, +s: Nat, +k: Nat) -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, Nat.add(s, k), k), List.drop(&2, Nat, List.drop(&2, Nat, ps, Nat.add(s, k)), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  +d = List.drop(&2, Nat, ps, Nat.add(s, k))
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, d, k), List.drop(&2, Nat, d, k)), d, ps.take_drop(d, k)) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  %ps.drop_drop(ps, s, k) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  ps.take_drop(List.drop(&2, Nat, ps, s), k)
