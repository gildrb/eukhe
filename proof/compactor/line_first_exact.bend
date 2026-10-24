# eukhe: the proof of LAW line_first_exact
# Text.eq compares char by char as the spec does (lfx.eq, by induction);
# two characters are equal exactly when their widths are.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def lfx.w(x: C.W, y: C.W) -> {Nat.is_eq(Compactor.w_tag(x), Compactor.w_tag(y)) == C.W.eq(x, y) : Bool}:
  match x:
    case C.W1{}:
      match y:
        case C.W1{}:
          {==}
        case C.W2{}:
          {==}
        case C.W3{}:
          {==}
        case C.W4{}:
          {==}
    case C.W2{}:
      match y:
        case C.W1{}:
          {==}
        case C.W2{}:
          {==}
        case C.W3{}:
          {==}
        case C.W4{}:
          {==}
    case C.W3{}:
      match y:
        case C.W1{}:
          {==}
        case C.W2{}:
          {==}
        case C.W3{}:
          {==}
        case C.W4{}:
          {==}
    case C.W4{}:
      match y:
        case C.W1{}:
          {==}
        case C.W2{}:
          {==}
        case C.W3{}:
          {==}
        case C.W4{}:
          {==}

def lfx.eq(a: List<&2, C.W>, b: List<&2, C.W>) -> {C.Text.eq(a, b) == Compactor.same_spec(a, b) : Bool}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case y <> ys:
          {==}
    case +x <> +xs:
      match b:
        case Nil{}:
          {==}
        case +y <> +ys:
          %Equal.sym(Bool, C.Text.eq(xs, ys), Compactor.same_spec(xs, ys), lfx.eq(xs, ys)) : {Bool.and(C.W.eq(x, y), _) == Bool.and(Nat.is_eq(Compactor.w_tag(x), Compactor.w_tag(y)), Compactor.same_spec(xs, ys)) : Bool}
          %lfx.w(x, y) : {Bool.and(_, Compactor.same_spec(xs, ys)) == Bool.and(Nat.is_eq(Compactor.w_tag(x), Compactor.w_tag(y)), Compactor.same_spec(xs, ys)) : Bool}
          {==}

def Compactor.line_first_exact(want, got):
  match want:
    case None{}:
      {==}
    case Some{f}:
      match got:
        case None{}:
          {==}
        case Some{g}:
          lfx.eq(f, g)
