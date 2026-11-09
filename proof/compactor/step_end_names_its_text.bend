# eukhe: the proof of LAW step_end_names_its_text
# Case by case on the line's tries left, the reply, whether it fits and
# whether it is shorter: each end carries the reply just read, the best
# reply the line holds, or its input, under the tag that names it.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

# an end with the best reply, else the input
def sen.end(-c: Nat, b: Maybe<&2, List<&2, C.W>>, -said: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>) -> Compactor.NextNames(C.Ends{c, C.end.of(b, input)}, said, b, input):
  match b:
    case None{}:
      {==}
    case Some{a}:
      {==}

def sen.says(fit: Bool, less: Bool, p: Nat, -made: Nat, -node: Nat, b: Maybe<&2, List<&2, C.W>>, -input: List<&2, C.W>, -ws: List<&2, C.W>, -len: Nat) -> Compactor.NextNames(C.line.says(fit, less, p, made, node, b, input, ws, len), Some{ws}, b, input):
  match fit less:
    case True{} y:
      {==}
    case False{} False{}:
      sen.end(1n+made, b, Some{ws}, input)
    case False{} True{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          Unit{}

def Compactor.step_end_names_its_text(left, made, node, best, bl, input, r):
  match left:
    case 0n:
      sen.end(made, best, Compactor.said_text(r), input)
    case 1n+p:
      match r:
        case C.Erred{}:
          Unit{}
        case C.Says{ws}:
          match ws:
            case Nil{}:
              sen.end(1n+made, best, Some{Nil{}}, input)
            case +w <> +t:
              sen.says(Nat.is_le(C.Text.len(w <> t), node), C.shorter(C.Text.len(w <> t), best, bl), p, made, node, best, input, w <> t, C.Text.len(w <> t))
