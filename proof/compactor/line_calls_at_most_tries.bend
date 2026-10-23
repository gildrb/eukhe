# eukhe: the proof of LAW line_calls_at_most_tries

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/nat/is_le.bend as LNatIsLe

# (H1) A line
# -----------

def pc.calls_next(fit: Bool, less: Bool, -ws: List<&2, C.W>, -node: Nat, -best: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, rec: C.Line, p: Nat, ih: {Nat.is_le(C.Line.calls(rec), p) == True{} : Bool}) -> {Nat.is_le(C.Line.calls(C.line.next(fit, less, ws, node, best, input, rec)), 1n+p) == True{} : Bool}:
  match fit less:
    case True{} l:
      LNatIsLe.compactor.pc.le_zero(p)
    case False{} False{}:
      LNatIsLe.compactor.pc.le_zero(p)
    case False{} True{}:
      match rec:
        case C.Line{c, l}:
          ih

def pc.calls_go(tries: Nat, +node: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, rs: List<&2, C.Reply>, +input: List<&2, C.W>) -> {Nat.is_le(C.Line.calls(C.line.go(tries, node, best, bl, rs, input)), tries) == True{} : Bool}:
  match tries:
    case 0n:
      {==}
    case 1n+p:
      match rs:
        case Nil{}:
          LNatIsLe.compactor.pc.le_zero(p)
        case r <> +rest:
          match r:
            case C.Erred{}:
              LNatIsLe.compactor.pc.le_zero(p)
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  LNatIsLe.compactor.pc.le_zero(p)
                case +w <> +t:
                  +q = p
                  +len = C.Text.len(w <> t)
                  pc.calls_next(Nat.is_le(len, node), C.shorter(len, best, bl), w <> t, node, best, input, C.line.go(q, node, Some{w <> t}, len, rest, input), q, pc.calls_go(q, node, Some{w <> t}, len, rest, input))

def pc.line_calls_at_most_tries(+tries: Nat, +node: Nat, +input: List<&2, C.W>, rs: List<&2, C.Reply>) -> {Nat.is_le(C.Line.calls(C.line(tries, node, input, rs)), tries) == True{} : Bool}:
  pc.calls_go(tries, node, None{}, 0n, rs, input)

# (H1) A compactor call always ends with a line that fits

def Compactor.line_calls_at_most_tries(tries, node, input, rs):
  pc.line_calls_at_most_tries(tries, node, input, rs)
