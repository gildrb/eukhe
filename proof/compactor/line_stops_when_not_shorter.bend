# eukhe: the proof of LAW line_stops_when_not_shorter

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base.bend as L

def pc.le_not_lt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      L.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_not_lt(p, q, e)

def pc.lt_le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      L.pc.absurd_ft({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 1n+p 0n _:
      L.pc.absurd_ft({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 0n 1n+q 0n:
      L.pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      L.pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pc.lt_le_trans(p, q, r, ab, bc)

def pc.stop_next(fa: Bool, fb: Bool, lb: Bool, -a: List<&2, C.W>, -b: List<&2, C.W>, -node: Nat, -input: List<&2, C.W>, -rec: C.Line, ea: {fa == False{} : Bool}, eb: {fb == False{} : Bool}, el: {lb == False{} : Bool}) -> {C.line.next(fa, True{}, a, node, None{}, input, C.line.next(fb, lb, b, node, Some{a}, input, rec)) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}:
  match fa fb lb:
    case True{} y z:
      L.pc.absurd_tf({C.Line{1n, Some{a}} == C.Line{2n, Some{C.cut(a, node)}} : C.Line}, ea)
    case False{} True{} z:
      L.pc.absurd_tf({C.Line{2n, Some{b}} == C.Line{2n, Some{C.cut(a, node)}} : C.Line}, eb)
    case False{} False{} True{}:
      L.pc.absurd_tf({C.Line.more(C.Line.more(rec)) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}, el)
    case False{} False{} False{}:
      {==}

def pc.line_stops_when_not_shorter(+t: Nat, +node: Nat, +input: List<&2, C.W>, +a: List<&2, C.W>, +b: List<&2, C.W>, +rest: List<&2, C.Reply>, +over: {Nat.is_lt(node, C.Text.len(a)) == True{} : Bool}, +longer: {Nat.is_le(C.Text.len(a), C.Text.len(b)) == True{} : Bool}) -> {C.line(2n+t, node, input, C.Says{a} <> C.Says{b} <> rest) == C.Line{2n, Some{C.cut(a, node)}} : C.Line}:
  match a:
    case Nil{}:
      L.pc.lt_zero({C.line(2n+t, node, input, C.Says{Nil{}} <> C.Says{b} <> rest) == C.Line{2n, Some{C.cut(Nil{}, node)}} : C.Line}, node, over)
    case +x <> +y:
      match b:
        case Nil{}:
          L.pc.lt_zero({C.line(2n+t, node, input, C.Says{x <> y} <> C.Says{Nil{}} <> rest) == C.Line{2n, Some{C.cut(x <> y, node)}} : C.Line}, node, pc.lt_le_trans(node, C.Text.len(x <> y), 0n, over, longer))
        case +u <> +v:
          pc.stop_next(Nat.is_le(C.Text.len(x <> y), node), Nat.is_le(C.Text.len(u <> v), node), Nat.is_lt(C.Text.len(u <> v), C.Text.len(x <> y)), x <> y, u <> v, node, input, C.line.go(t, node, Some{u <> v}, C.Text.len(u <> v), rest, input), L.pc.lt_not_le(node, C.Text.len(x <> y), over), L.pc.lt_not_le(node, C.Text.len(u <> v), pc.lt_le_trans(node, C.Text.len(x <> y), C.Text.len(u <> v), over, longer)), pc.le_not_lt(C.Text.len(x <> y), C.Text.len(u <> v), longer))

def Compactor.line_stops_when_not_shorter(t, node, input, a, b, rest, over, longer):
  pc.line_stops_when_not_shorter(t, node, input, a, b, rest, over, longer)
