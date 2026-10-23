# eukhe: the proof of LAW quirk_unknown_rejected

import Base
import ../../bend/infer.bend as If
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Compiling
# ---------

def pq.ka_app(pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, +known: List<&2, Nat>, bad: {If.elem(known, If.Rule.dir(r)) == False{} : Bool}) -> {If.known_all(List.append(&2, If.Rule, pre, r <> post), known) == False{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, If.elem(known, If.Rule.dir(r)), False{}, bad) : {Bool.and(_, If.known_all(post, known)) == False{} : Bool}
      {==}
    case +h <> +t:
      %Equal.sym(Bool, If.known_all(List.append(&2, If.Rule, t, r <> post), known), False{}, pq.ka_app(t, r, post, known, bad)) : {Bool.and(If.elem(known, If.Rule.dir(h)), _) == False{} : Bool}
      LA.pq.and_f(If.elem(known, If.Rule.dir(h)))

def pq.quirk_unknown_rejected(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +r: If.Rule, +post: List<&2, If.Rule>, bad: {If.elem(known, If.Rule.dir(r)) == False{} : Bool}) -> {If.compiles(known, List.append(&2, If.Rule, pre, r <> post)) == False{} : Bool}:
  %Equal.sym(Bool, If.known_all(List.append(&2, If.Rule, pre, r <> post), known), False{}, pq.ka_app(pre, r, post, known, bad)) : {Bool.and(_, Bool.not(If.ambiguous(List.append(&2, If.Rule, pre, r <> post)))) == False{} : Bool}
  {==}

# (S6) The inference layer

def Laws.quirk_unknown_rejected(known, pre, r, post, bad):
  pq.quirk_unknown_rejected(known, pre, r, post, bad)
