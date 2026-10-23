# eukhe: the proof of LAW quirk_compile_order_free

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer

def pq.and_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pq.or_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pq.or4(c: Bool, +x: Bool, +y: Bool, +z: Bool) -> {Bool.or(Bool.or(c, x), Bool.or(y, z)) == Bool.or(Bool.or(c, y), Bool.or(x, z)) : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      pq.or_swap(x, y, z)

def pq.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pq.eq_comm(p, q)

def pq.ka_swap(pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>, +known: List<&2, Nat>) -> {If.known_all(List.append(&2, If.Rule, pre, b <> a <> post), known) == If.known_all(List.append(&2, If.Rule, pre, a <> b <> post), known) : Bool}:
  match pre:
    case Nil{}:
      pq.and_swap(If.elem(known, If.Rule.dir(b)), If.elem(known, If.Rule.dir(a)), If.known_all(post, known))
    case +h <> +t:
      %pq.ka_swap(t, a, b, post, known) : {Bool.and(If.elem(known, If.Rule.dir(h)), If.known_all(List.append(&2, If.Rule, t, b <> a <> post), known)) == Bool.and(If.elem(known, If.Rule.dir(h)), _) : Bool}
      {==}

def pq.cl_app_swap(+s: If.Rule, pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>) -> {If.clashes(s, List.append(&2, If.Rule, pre, b <> a <> post)) == If.clashes(s, List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}:
  match pre:
    case Nil{}:
      pq.or_swap(If.clash(s, b), If.clash(s, a), If.clashes(s, post))
    case +h <> +t:
      %pq.cl_app_swap(s, t, a, b, post) : {Bool.or(If.clash(s, h), If.clashes(s, List.append(&2, If.Rule, t, b <> a <> post))) == Bool.or(If.clash(s, h), _) : Bool}
      {==}

def pq.clash_sym(a: If.Rule, b: If.Rule) -> {If.clash(a, b) == If.clash(b, a) : Bool}:
  match a b:
    case If.Rule{+la, +ta, +da, +va} If.Rule{+lb, +tb, +db, +vb}:
      +ka = If.Lay.rank(la)
      +kb = If.Lay.rank(lb)
      +C = If.clash(If.Rule{la, ta, da, va}, If.Rule{lb, tb, db, vb})
      %pq.eq_comm(ka, kb) : {C == Bool.and(_, Bool.and(Nat.is_eq(tb, ta), Bool.and(Nat.is_eq(db, da), Bool.not(Nat.is_eq(vb, va))))) : Bool}
      %pq.eq_comm(ta, tb) : {C == Bool.and(Nat.is_eq(ka, kb), Bool.and(_, Bool.and(Nat.is_eq(db, da), Bool.not(Nat.is_eq(vb, va))))) : Bool}
      %pq.eq_comm(da, db) : {C == Bool.and(Nat.is_eq(ka, kb), Bool.and(Nat.is_eq(ta, tb), Bool.and(_, Bool.not(Nat.is_eq(vb, va))))) : Bool}
      %pq.eq_comm(va, vb) : {C == Bool.and(Nat.is_eq(ka, kb), Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(_)))) : Bool}
      {==}

def pq.amb_swap(pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>) -> {If.ambiguous(List.append(&2, If.Rule, pre, b <> a <> post)) == If.ambiguous(List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}:
  match pre:
    case Nil{}:
      %pq.clash_sym(a, b) : {Bool.or(Bool.or(_, If.clashes(b, post)), Bool.or(If.clashes(a, post), If.ambiguous(post))) == Bool.or(Bool.or(If.clash(a, b), If.clashes(a, post)), Bool.or(If.clashes(b, post), If.ambiguous(post))) : Bool}
      pq.or4(If.clash(a, b), If.clashes(b, post), If.clashes(a, post), If.ambiguous(post))
    case +h <> +t:
      +X1 = List.append(&2, If.Rule, t, b <> a <> post)
      +X2 = List.append(&2, If.Rule, t, a <> b <> post)
      %pq.cl_app_swap(h, t, a, b, post) : {Bool.or(If.clashes(h, X1), If.ambiguous(X1)) == Bool.or(_, If.ambiguous(X2)) : Bool}
      %pq.amb_swap(t, a, b, post) : {Bool.or(If.clashes(h, X1), If.ambiguous(X1)) == Bool.or(If.clashes(h, X1), _) : Bool}
      {==}

def pq.quirk_compile_order_free(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>) -> {If.compiles(known, List.append(&2, If.Rule, pre, b <> a <> post)) == If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) : Bool}:
  +L1 = List.append(&2, If.Rule, pre, b <> a <> post)
  +L2 = List.append(&2, If.Rule, pre, a <> b <> post)
  %pq.ka_swap(pre, a, b, post, known) : {Bool.and(If.known_all(L1, known), Bool.not(If.ambiguous(L1))) == Bool.and(_, Bool.not(If.ambiguous(L2))) : Bool}
  %pq.amb_swap(pre, a, b, post) : {Bool.and(If.known_all(L1, known), Bool.not(If.ambiguous(L1))) == Bool.and(If.known_all(L1, known), Bool.not(_)) : Bool}
  {==}

def Infer.quirk_compile_order_free(known, pre, a, b, post):
  pq.quirk_compile_order_free(known, pre, a, b, post)
