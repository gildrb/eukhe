# eukhe: the proof of LAW line_step_exact
# A text's Text.len is its bytes (lse.len); then line.step and the spec
# take the same branch on every state and reply.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

# a text's length is its bytes
def lse.len(t: List<&2, C.W>) -> {C.Text.len(t) == Compactor.bytes(t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case C.W1{}:
          %lse.len(rest) : {1n+C.Text.len(rest) == 1n+_ : Nat}
          {==}
        case C.W2{}:
          %lse.len(rest) : {2n+C.Text.len(rest) == 2n+_ : Nat}
          {==}
        case C.W3{}:
          %lse.len(rest) : {3n+C.Text.len(rest) == 3n+_ : Nat}
          {==}
        case C.W4{}:
          %lse.len(rest) : {4n+C.Text.len(rest) == 4n+_ : Nat}
          {==}

def lse.long(less: Bool, q: Nat, +m: Nat, +n: Nat, -t: List<&2, C.W>, +i: List<&2, C.W>, +ws: List<&2, C.W>, +len: Nat) -> {C.line.says(False{}, less, q, m, n, Some{t}, i, ws, len) == Compactor.step_spec.long(less, q, m, n, Some{t}, i, ws, len) : C.Next}:
  match less:
    case False{}:
      {==}
    case True{}:
      match q:
        case 0n:
          {==}
        case 1n+k:
          {==}

# a reply of len bytes with q tries left after it
def lse.says(fit: Bool, b: Maybe<&2, List<&2, C.W>>, +bl: Nat, q: Nat, +m: Nat, +n: Nat, +i: List<&2, C.W>, +ws: List<&2, C.W>, +len: Nat) -> {C.line.says(fit, C.shorter(len, b, bl), q, m, n, b, i, ws, len) == Compactor.step_spec.text(fit, Compactor.shorter_spec(b, bl, len), q, m, n, b, i, ws, len) : C.Next}:
  match fit:
    case True{}:
      {==}
    case False{}:
      match b:
        case None{}:
          match q:
            case 0n:
              {==}
            case 1n+k:
              {==}
        case Some{t}:
          lse.long(Nat.is_lt(len, bl), q, m, n, t, i, ws, len)

def lse.text(q: Nat, +m: Nat, +n: Nat, +b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +i: List<&2, C.W>, +ws: List<&2, C.W>) -> {C.line.says(Nat.is_le(C.Text.len(ws), n), C.shorter(C.Text.len(ws), b, bl), q, m, n, b, i, ws, C.Text.len(ws)) == Compactor.step_spec.text(Nat.is_le(Compactor.bytes(ws), n), Compactor.shorter_spec(b, bl, Compactor.bytes(ws)), q, m, n, b, i, ws, Compactor.bytes(ws)) : C.Next}:
  %Equal.sym(Nat, C.Text.len(ws), Compactor.bytes(ws), lse.len(ws)) : {C.line.says(Nat.is_le(_, n), C.shorter(_, b, bl), q, m, n, b, i, ws, _) == Compactor.step_spec.text(Nat.is_le(Compactor.bytes(ws), n), Compactor.shorter_spec(b, bl, Compactor.bytes(ws)), q, m, n, b, i, ws, Compactor.bytes(ws)) : C.Next}
  lse.says(Nat.is_le(Compactor.bytes(ws), n), b, bl, q, m, n, i, ws, Compactor.bytes(ws))

# a line that ends with the best reply, else the input, cut
def lse.end(-c: Nat, b: Maybe<&2, List<&2, C.W>>, -i: List<&2, C.W>) -> {C.Ends{c, C.end.of(b, i)} == C.Ends{c, Compactor.end_spec(b, i)} : C.Next}:
  match b:
    case None{}:
      {==}
    case Some{t}:
      {==}

def Compactor.line_step_exact(st, r):
  match st:
    case C.Lst{l, m, +n, +b, +bl, +i}:
      match l:
        case 0n:
          lse.end(m, b, i)
        case 1n+q:
          match r:
            case C.Erred{}:
              {==}
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  lse.end(1n+m, b, i)
                case +c <> +t:
                  lse.text(q, m, n, b, bl, i, c <> t)
