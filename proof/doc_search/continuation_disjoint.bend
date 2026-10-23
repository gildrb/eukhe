# eukhe: the proof of LAW continuation_disjoint

import Base
import ../../bend/doc_search.bend as Sr
import ../../LAWS.bend as Laws
import ./base.bend as LA

# ==== search ====
# proof_doc_search: the grep and continuation laws of LAWS.bend section documents
# (F6, F7): grep puts every walked entry in exactly one class, has a
# notice of each class it left out exactly when that class is not empty,
# and a notice for each shown file it cut; a continuation gives a page
# that is not empty, follows on from the page before it with nothing left
# out and nothing twice, and has no item in common with it.
# Logic and numbers
# -----------------

def documents.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def documents.ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : documents.ps.BD(_, Unit, A)
  Unit{}

def documents.ps.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      documents.ps.absurd({0n == 1n+q : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 0n:
      documents.ps.absurd({1n+p == 0n : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      %documents.ps.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def documents.ps.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      documents.ps.absurd({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def documents.ps.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      documents.ps.absurd({False{} == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def documents.ps.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      documents.ps.absurd({True{} == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case False{}:
      {==}

def ps.or_fr(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      documents.ps.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def documents.ps.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ps.or_mono(a: Bool, -x: Bool, -y: Bool, h: {Bool.or(a, x) == True{} : Bool}, f: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def ps.mem_app(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {Bool.or(Sr.mem(n, a), Sr.mem(n, b)) == Sr.mem(n, List.append(&2, Nat, a, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ps.mem_app(n, rest, b) : {Bool.or(Bool.or(Nat.is_eq(x, n), Sr.mem(n, rest)), Sr.mem(n, b)) == Bool.or(Nat.is_eq(x, n), _) : Bool}
      documents.ps.or_assoc(Nat.is_eq(x, n), Sr.mem(n, rest), Sr.mem(n, b))

def ps.mem_app_l(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, h: {Sr.mem(n, a) == True{} : Bool}) -> {Sr.mem(n, List.append(&2, Nat, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      documents.ps.absurd({Sr.mem(n, b) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case +x <> +rest:
      ps.or_mono(Nat.is_eq(x, n), Sr.mem(n, rest), Sr.mem(n, List.append(&2, Nat, rest, b)), h, hh => ps.mem_app_l(n, rest, b, hh))

def ps.nodup_drop(xs: List<&2, Nat>, s: Nat, nd: {Sr.nodup(xs) == True{} : Bool}) -> {Sr.nodup(List.drop(&2, Nat, xs, s)) == True{} : Bool}:
  match xs s:
    case Nil{} s:
      {==}
    case h <> t 0n:
      nd
    case +h <> +t 1n+p:
      ps.nodup_drop(t, p, documents.ps.and_r(Bool.not(Sr.mem(h, t)), Sr.nodup(t), nd))

def ps.nd_hit(-y: Nat, +x: Nat, e: {y == x : Nat}, +t: List<&2, Nat>, +b: List<&2, Nat>, ny: {Sr.mem(y, List.append(&2, Nat, t, b)) == False{} : Bool}) -> {Bool.or(Sr.mem(x, t), Sr.mem(x, b)) == False{} : Bool}:
  %Equal.sym(Bool, Bool.or(Sr.mem(x, t), Sr.mem(x, b)), Sr.mem(x, List.append(&2, Nat, t, b)), ps.mem_app(x, t, b)) : {_ == False{} : Bool}
  %e : {Sr.mem(_, List.append(&2, Nat, t, b)) == False{} : Bool}
  ny

def ps.nd_step(+y: Nat, +x: Nat, q: Bool, eq: {Nat.is_eq(y, x) == q : Bool}, +t: List<&2, Nat>, +b: List<&2, Nat>, ny: {Sr.mem(y, List.append(&2, Nat, t, b)) == False{} : Bool}, ih: {Bool.and(Sr.mem(x, t), Sr.mem(x, b)) == False{} : Bool}) -> {Bool.and(Bool.or(q, Sr.mem(x, t)), Sr.mem(x, b)) == False{} : Bool}:
  match q:
    case True{}:
      ps.or_fr(Sr.mem(x, t), Sr.mem(x, b), ps.nd_hit(y, x, documents.ps.eq_true(y, x, eq), t, b, ny))
    case False{}:
      ih

def ps.nd_app(a: List<&2, Nat>, +b: List<&2, Nat>, +x: Nat, +nd: {Sr.nodup(List.append(&2, Nat, a, b)) == True{} : Bool}) -> {Bool.and(Sr.mem(x, a), Sr.mem(x, b)) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +y <> +t:
      +ab = List.append(&2, Nat, t, b)
      +ny = documents.ps.not_t(Sr.mem(y, ab), documents.ps.and_l(Bool.not(Sr.mem(y, ab)), Sr.nodup(ab), nd))
      ps.nd_step(y, x, Nat.is_eq(y, x), {==}, t, b, ny, ps.nd_app(t, b, x, documents.ps.and_r(Bool.not(Sr.mem(y, ab)), Sr.nodup(ab), nd)))

def ps.and_imp(a: Bool, b: Bool, -c: Bool, h: {Bool.and(a, c) == False{} : Bool}, f: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      documents.ps.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, c, False{}, Equal.sym(Bool, c, True{}, f({==})), h))

def ps.disj_at(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +x: Nat, nd: {Sr.nodup(ps) == True{} : Bool}) -> {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, Nat.add(s, k), k))) == False{} : Bool}:
  +p1 = Sr.page(ps, s, k)
  +p2 = Sr.page(ps, Nat.add(s, k), k)
  +r = List.drop(&2, Nat, List.drop(&2, Nat, ps, Nat.add(s, k)), k)
  +all = List.append(&2, Nat, p1, List.append(&2, Nat, p2, r))
  +whole = Equal.trans(Bool, Sr.nodup(all), Sr.nodup(List.drop(&2, Nat, ps, s)), True{}, Equal.cong(List<&2, Nat>, Bool, l => Sr.nodup(l), all, List.drop(&2, Nat, ps, s), LA.ps.contig(ps, s, k)), ps.nodup_drop(ps, s, nd))
  ps.and_imp(Sr.mem(x, p1), Sr.mem(x, p2), Sr.mem(x, List.append(&2, Nat, p2, r)), ps.nd_app(p1, List.append(&2, Nat, p2, r), x, whole), hh => ps.mem_app_l(x, p2, r, hh))

# the law continuation_disjoint
def ps.disjoint(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, +x: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}, nd: {Sr.nodup(ps) == True{} : Bool}) -> {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, c, k))) == False{} : Bool}:
  %LA.ps.next_c(ps, s, k, c, h) : {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, _, k))) == False{} : Bool}
  ps.disj_at(ps, s, k, x, nd)

def Laws.continuation_disjoint(ps, s, k, c, x, h, nd):
  ps.disjoint(ps, s, k, c, x, h, nd)
