# eukhe: the proof of LAW line_takes_first_fit
# Induction on the tries. A reply the line reads fits exactly when the
# laws' first_fit counts it (its bytes are its Text.len, and a text that
# is not empty has more than 0 of them: ftf.fit); the line stops at the
# first that fits and takes it, and reads no reply after one that ends
# it otherwise.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ./base.bend as LA

def ftf.pos(w: C.W, -t: List<&2, C.W>) -> {Nat.is_lt(0n, Compactor.bytes(w <> t)) == True{} : Bool}:
  match w:
    case C.W1{}:
      {==}
    case C.W2{}:
      {==}
    case C.W3{}:
      {==}
    case C.W4{}:
      {==}

# the laws' fit of a text that is not empty is line.go's
def ftf.fit(+w: C.W, +t: List<&2, C.W>, +node: Nat) -> {Bool.and(Nat.is_lt(0n, Compactor.bytes(w <> t)), Nat.is_le(Compactor.bytes(w <> t), node)) == Nat.is_le(C.Text.len(w <> t), node) : Bool}:
  %Equal.sym(Bool, Nat.is_lt(0n, Compactor.bytes(w <> t)), True{}, ftf.pos(w, t)) : {Bool.and(_, Nat.is_le(Compactor.bytes(w <> t), node)) == Nat.is_le(C.Text.len(w <> t), node) : Bool}
  %Equal.sym(Nat, C.Text.len(w <> t), Compactor.bytes(w <> t), LA.lp.len(w <> t)) : {Nat.is_le(Compactor.bytes(w <> t), node) == Nat.is_le(_, node) : Bool}
  {==}

# no reply read after the first: no fit read
def ftf.none(rs: List<&2, C.Reply>, +node: Nat, -got: Maybe<&2, List<&2, C.W>>) -> Compactor.FirstIs(Compactor.first_fit(node, List.take(&2, C.Reply, rs, 0n)), got):
  match rs:
    case Nil{}:
      Unit{}
    case r <> rest:
      Unit{}

# the laws' fit of the reply read is the line's: fit
def ftf.pick(fit: Bool, +w: C.W, +t: List<&2, C.W>, +node: Nat, efit: {fit == Nat.is_le(C.Text.len(w <> t), node) : Bool}) -> {fit == Bool.and(Nat.is_lt(0n, Compactor.bytes(w <> t)), Nat.is_le(Compactor.bytes(w <> t), node)) : Bool}:
  Equal.trans(Bool, fit, Nat.is_le(C.Text.len(w <> t), node), Bool.and(Nat.is_lt(0n, Compactor.bytes(w <> t)), Nat.is_le(Compactor.bytes(w <> t), node)), efit, Equal.sym(Bool, Bool.and(Nat.is_lt(0n, Compactor.bytes(w <> t)), Nat.is_le(Compactor.bytes(w <> t), node)), Nat.is_le(C.Text.len(w <> t), node), ftf.fit(w, t, node)))

def ftf.next(fit: Bool, less: Bool, +w: C.W, +t: List<&2, C.W>, +node: Nat, -best: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, +rest: List<&2, C.Reply>, rec: C.Line, efit: {fit == Nat.is_le(C.Text.len(w <> t), node) : Bool}, ih: Compactor.FirstIs(Compactor.first_fit(node, List.take(&2, C.Reply, rest, C.Line.calls(rec))), C.Line.line(rec))) -> Compactor.FirstIs(Compactor.first_fit(node, List.take(&2, C.Reply, C.Says{w <> t} <> rest, C.Line.calls(C.line.next(fit, less, w <> t, node, best, input, rec)))), C.Line.line(C.line.next(fit, less, w <> t, node, best, input, rec))):
  match fit less:
    case True{} l:
      %ftf.pick(True{}, w, t, node, efit) : Compactor.FirstIs(Compactor.first_fit.pick(_, w <> t, Compactor.first_fit(node, List.take(&2, C.Reply, rest, 0n))), Some{w <> t})
      {==}
    case False{} False{}:
      %ftf.pick(False{}, w, t, node, efit) : Compactor.FirstIs(Compactor.first_fit.pick(_, w <> t, Compactor.first_fit(node, List.take(&2, C.Reply, rest, 0n))), Some{C.line.end(node, best, input)})
      ftf.none(rest, node, Some{C.line.end(node, best, input)})
    case False{} True{}:
      match rec:
        case C.Line{n, l}:
          %ftf.pick(False{}, w, t, node, efit) : Compactor.FirstIs(Compactor.first_fit.pick(_, w <> t, Compactor.first_fit(node, List.take(&2, C.Reply, rest, n))), l)
          ih

def ftf.go(tries: Nat, +node: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, rs: List<&2, C.Reply>, +input: List<&2, C.W>) -> Compactor.FirstIs(Compactor.first_fit(node, List.take(&2, C.Reply, rs, C.Line.calls(C.line.go(tries, node, best, bl, rs, input)))), C.Line.line(C.line.go(tries, node, best, bl, rs, input))):
  match tries:
    case 0n:
      ftf.none(rs, node, Some{C.line.end(node, best, input)})
    case 1n+p:
      match rs:
        case Nil{}:
          Unit{}
        case r <> +rest:
          match r:
            case C.Erred{}:
              ftf.none(rest, node, None{})
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  ftf.none(rest, node, Some{C.line.end(node, best, input)})
                case +w <> +t:
                  +q = p
                  +len = C.Text.len(w <> t)
                  ftf.next(Nat.is_le(len, node), C.shorter(len, best, bl), w, t, node, best, input, rest, C.line.go(q, node, Some{w <> t}, len, rest, input), {==}, ftf.go(q, node, Some{w <> t}, len, rest, input))

def Compactor.line_takes_first_fit(tries, node, input, rs):
  ftf.go(tries, node, None{}, 0n, rs, input)
