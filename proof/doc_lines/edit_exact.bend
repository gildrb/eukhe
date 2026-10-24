# eukhe: the proof of LAW edit_exact: the new lines are the spec's fresh
# pieces, the rest is the edit itself

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

def ee.fresh(xs: List<&2, List<&2, Dl.B>>) -> {Dl.fresh(xs) == DocLines.lines.Fresh(xs) : List<&2, Dl.Piece>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, Dl.Piece>, List<&2, Dl.Piece>, l => Dl.Piece{x, None{}} <> l, Dl.fresh(rest), DocLines.lines.Fresh(rest), ee.fresh(rest))

def DocLines.edit_exact(b, c, ps, s, k, xs):
  Equal.cong(List<&2, Dl.Piece>, Dl.Ed, f => Dl.Ed{b, c, List.append(&2, Dl.Piece, List.take(&2, Dl.Piece, ps, s), List.append(&2, Dl.Piece, f, List.drop(&2, Dl.Piece, ps, Nat.add(s, k))))}, Dl.fresh(xs), DocLines.lines.Fresh(xs), ee.fresh(xs))
