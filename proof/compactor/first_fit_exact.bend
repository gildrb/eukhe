# eukhe: the proof of LAW first_fit_exact
# Induction on the replies; a text reply's Text.len is its bytes
# (PLSE.lse.len), and a text that is not empty has more than 0 bytes.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ./line_step_exact.bend as PLSE

def ffe.pick(b: Bool, -t: List<&2, C.W>, -rec: Maybe<&2, List<&2, C.W>>) -> {C.first_fit.pick(b, t, rec) == Compactor.first_fit_spec.pick(b, t, rec) : Maybe<&2, List<&2, C.W>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ffe.pos(w: C.W, -t: List<&2, C.W>) -> {True{} == Nat.is_lt(0n, Compactor.bytes(w <> t)) : Bool}:
  match w:
    case C.W1{}:
      {==}
    case C.W2{}:
      {==}
    case C.W3{}:
      {==}
    case C.W4{}:
      {==}

def ffe.go(+node: Nat, rs: List<&2, C.Reply>) -> {C.first_fit(node, rs) == Compactor.first_fit_spec(node, rs) : Maybe<&2, List<&2, C.W>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case C.Erred{}:
          ffe.go(node, rest)
        case C.Says{ws}:
          match ws:
            case Nil{}:
              ffe.go(node, rest)
            case +w <> +t:
              %Equal.sym(Maybe<&2, List<&2, C.W>>, C.first_fit(node, rest), Compactor.first_fit_spec(node, rest), ffe.go(node, rest)) : {C.first_fit.pick(Nat.is_le(C.Text.len(w <> t), node), w <> t, _) == Compactor.first_fit_spec.pick(Bool.and(Nat.is_lt(0n, Compactor.bytes(w <> t)), Nat.is_le(Compactor.bytes(w <> t), node)), w <> t, Compactor.first_fit_spec(node, rest)) : Maybe<&2, List<&2, C.W>>}
              %Equal.sym(Nat, C.Text.len(w <> t), Compactor.bytes(w <> t), PLSE.lse.len(w <> t)) : {C.first_fit.pick(Nat.is_le(_, node), w <> t, Compactor.first_fit_spec(node, rest)) == Compactor.first_fit_spec.pick(Bool.and(Nat.is_lt(0n, Compactor.bytes(w <> t)), Nat.is_le(Compactor.bytes(w <> t), node)), w <> t, Compactor.first_fit_spec(node, rest)) : Maybe<&2, List<&2, C.W>>}
              %ffe.pos(w, t) : {C.first_fit.pick(Nat.is_le(Compactor.bytes(w <> t), node), w <> t, Compactor.first_fit_spec(node, rest)) == Compactor.first_fit_spec.pick(Bool.and(_, Nat.is_le(Compactor.bytes(w <> t), node)), w <> t, Compactor.first_fit_spec(node, rest)) : Maybe<&2, List<&2, C.W>>}
              ffe.pick(Nat.is_le(Compactor.bytes(w <> t), node), w <> t, Compactor.first_fit_spec(node, rest))

def Compactor.first_fit_exact(node, rs):
  ffe.go(node, rs)
