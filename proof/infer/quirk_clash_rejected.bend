# eukhe: the proof of LAW quirk_clash_rejected

import Base
import ../../bend/infer.bend as If
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pq.or_tl(-a: Bool, -b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.or(_, b) == True{} : Bool}
  {==}

def pq.or_tr(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def pq.clashes_app(+a: If.Rule, mid: List<&2, If.Rule>, +b: If.Rule, +post: List<&2, If.Rule>, both: {If.clash(a, b) == True{} : Bool}) -> {If.clashes(a, List.append(&2, If.Rule, mid, b <> post)) == True{} : Bool}:
  match mid:
    case Nil{}:
      pq.or_tl(If.clash(a, b), If.clashes(a, post), both)
    case +s <> +t:
      pq.or_tr(If.clash(a, s), If.clashes(a, List.append(&2, If.Rule, t, b <> post)), pq.clashes_app(a, t, b, post, both))

def pq.amb_app(pre: List<&2, If.Rule>, +a: If.Rule, +mid: List<&2, If.Rule>, +b: If.Rule, +post: List<&2, If.Rule>, both: {If.clash(a, b) == True{} : Bool}) -> {If.ambiguous(List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))) == True{} : Bool}:
  match pre:
    case Nil{}:
      +X = List.append(&2, If.Rule, mid, b <> post)
      pq.or_tl(If.clashes(a, X), If.ambiguous(X), pq.clashes_app(a, mid, b, post, both))
    case +h <> +t:
      +X = List.append(&2, If.Rule, t, a <> List.append(&2, If.Rule, mid, b <> post))
      pq.or_tr(If.clashes(h, X), If.ambiguous(X), pq.amb_app(t, a, mid, b, post, both))

def pq.quirk_clash_rejected(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +a: If.Rule, +mid: List<&2, If.Rule>, +b: If.Rule, +post: List<&2, If.Rule>, both: {If.clash(a, b) == True{} : Bool}) -> {If.compiles(known, List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))) == False{} : Bool}:
  +L = List.append(&2, If.Rule, pre, a <> List.append(&2, If.Rule, mid, b <> post))
  %Equal.sym(Bool, If.ambiguous(L), True{}, pq.amb_app(pre, a, mid, b, post, both)) : {Bool.and(If.known_all(L, known), Bool.not(_)) == False{} : Bool}
  LA.pq.and_f(If.known_all(L, known))

def Laws.quirk_clash_rejected(known, pre, a, mid, b, post, both):
  pq.quirk_clash_rejected(known, pre, a, mid, b, post, both)
