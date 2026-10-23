# eukhe: the proof of LAW line_takes_first_fit

import Base
import ../../bend/compactor.bend as C
import ../../LAWS.bend as Laws

def pc.text_eq_refl(t: List<&2, C.W>) -> {C.Text.eq(t, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case w <> r:
      match w:
        case C.W1{}:
          pc.text_eq_refl(r)
        case C.W2{}:
          pc.text_eq_refl(r)
        case C.W3{}:
          pc.text_eq_refl(r)
        case C.W4{}:
          pc.text_eq_refl(r)

def pc.first_next(fit: Bool, less: Bool, +w: C.W, +t: List<&2, C.W>, +node: Nat, -best: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, -rest: List<&2, C.Reply>, rec: C.Line, efit: {fit == Nat.is_le(C.Text.len(w <> t), node) : Bool}, ih: {C.line.first(C.first_fit(node, C.read(C.Line.calls(rec), rest)), C.Line.line(rec)) == True{} : Bool}) -> {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line.next(fit, less, w <> t, node, best, input, rec)), C.Says{w <> t} <> rest)), C.Line.line(C.line.next(fit, less, w <> t, node, best, input, rec))) == True{} : Bool}:
  match fit less:
    case True{} l:
      %efit : {C.line.first(C.first_fit.pick(_, w <> t, None{}), Some{w <> t}) == True{} : Bool}
      pc.text_eq_refl(w <> t)
    case False{} False{}:
      %efit : {C.line.first(C.first_fit.pick(_, w <> t, None{}), Some{C.line.end(node, best, input)}) == True{} : Bool}
      {==}
    case False{} True{}:
      match rec:
        case C.Line{n, l}:
          %efit : {C.line.first(C.first_fit.pick(_, w <> t, C.first_fit(node, C.read(n, rest))), l) == True{} : Bool}
          ih

def pc.first_go(tries: Nat, +node: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, rs: List<&2, C.Reply>, +input: List<&2, C.W>) -> {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line.go(tries, node, best, bl, rs, input)), rs)), C.Line.line(C.line.go(tries, node, best, bl, rs, input))) == True{} : Bool}:
  match tries:
    case 0n:
      {==}
    case 1n+p:
      match rs:
        case Nil{}:
          {==}
        case r <> +rest:
          match r:
            case C.Erred{}:
              {==}
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  {==}
                case +w <> +t:
                  +q = p
                  +len = C.Text.len(w <> t)
                  pc.first_next(Nat.is_le(len, node), C.shorter(len, best, bl), w, t, node, best, input, rest, C.line.go(q, node, Some{w <> t}, len, rest, input), {==}, pc.first_go(q, node, Some{w <> t}, len, rest, input))

def pc.line_takes_first_fit(+tries: Nat, +node: Nat, +input: List<&2, C.W>, +rs: List<&2, C.Reply>) -> {C.line.first(C.first_fit(node, C.read(C.Line.calls(C.line(tries, node, input, rs)), rs)), C.Line.line(C.line(tries, node, input, rs))) == True{} : Bool}:
  pc.first_go(tries, node, None{}, 0n, rs, input)

def Laws.line_takes_first_fit(tries, node, input, rs):
  pc.line_takes_first_fit(tries, node, input, rs)
