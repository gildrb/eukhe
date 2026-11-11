# eukhe: the proof of LAW persist_weaves_carry

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

# emit writes the pieces woven with the carry rule
def pln.emit(rest: List<&2, Dl.Piece>, +c: Dl.End, p: Dl.Piece) -> {Dl.emit(rest, c, p) == DocLines.lines.Weave.go(rest, p, DocLines.lines.Carry(DocLines.lines.Owns.go(rest, p), c)) : List<&2, Dl.B>}:
  match rest:
    case Nil{}:
      match p:
        case Dl.Piece{t, en}:
          {==}
    case +q <> +more:
      match p:
        case Dl.Piece{+t, en}:
          match en:
            case None{}:
              %pln.emit(more, c, q) : {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(c), Dl.emit(more, c, q))) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(c), _)) : List<&2, Dl.B>}
              {==}
            case Some{+e}:
              %pln.emit(more, e, q) : {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), Dl.emit(more, e, q))) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), _)) : List<&2, Dl.B>}
              {==}

def DocLines.persist_weaves_carry(ps, c):
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      pln.emit(rest, c, p)
