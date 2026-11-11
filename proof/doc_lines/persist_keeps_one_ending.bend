# eukhe: the proof of LAW persist_keeps_one_ending
#
# PROOF: piece by piece. A piece that owns no ending writes the carry e
# after it, one that owns e writes e and carries e on, one that owns the
# other ending contradicts the premise; so every separator is e, and the
# bytes with one more e are every text followed by e (pko.chain:
# associativity of append, the bytes of e).

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./base.bend as LA
import ./edit_keeps_untouched_bytes.bend as PEK

def pko.eb(e: Dl.End) -> {Dl.ebytes(e) == DocLines.lines.EndBytes(e) : List<&2, Dl.B>}:
  match e:
    case Dl.Lf{}:
      {==}
    case Dl.CrLf{}:
      {==}

# a piece t followed by the separator e, then the rest
def pko.chain(+t: List<&2, Dl.B>, +e: Dl.End, +q: Dl.Piece, +more: List<&2, Dl.Piece>, ih: {List.append(&2, Dl.B, Dl.emit(more, e, q), DocLines.lines.EndBytes(e)) == DocLines.lines.Each(DocLines.lines.Texts(q <> more), DocLines.lines.EndBytes(e)) : List<&2, Dl.B>}) -> {List.append(&2, Dl.B, List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), Dl.emit(more, e, q))), DocLines.lines.EndBytes(e)) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, DocLines.lines.EndBytes(e), DocLines.lines.Each(DocLines.lines.Texts(q <> more), DocLines.lines.EndBytes(e)))) : List<&2, Dl.B>}:
  +W = Dl.emit(more, e, q)
  +EB = DocLines.lines.EndBytes(e)
  +Z = DocLines.lines.Each(DocLines.lines.Texts(q <> more), EB)
  +eb = Dl.ebytes(e)
  %pko.eb(e) : {List.append(&2, Dl.B, List.append(&2, Dl.B, t, List.append(&2, Dl.B, eb, W)), EB) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, _, Z)) : List<&2, Dl.B>}
  %ih : {List.append(&2, Dl.B, List.append(&2, Dl.B, t, List.append(&2, Dl.B, eb, W)), EB) == List.append(&2, Dl.B, t, List.append(&2, Dl.B, eb, _)) : List<&2, Dl.B>}
  %PEK.pdl.app_assoc(Dl.B, eb, W, EB) : {List.append(&2, Dl.B, List.append(&2, Dl.B, t, List.append(&2, Dl.B, eb, W)), EB) == List.append(&2, Dl.B, t, _) : List<&2, Dl.B>}
  PEK.pdl.app_assoc(Dl.B, t, List.append(&2, Dl.B, eb, W), EB)

def pko.emit(ps: List<&2, Dl.Piece>, p: Dl.Piece, +e: Dl.End, h: {DocLines.lines.Owned(p <> ps, e) == True{} : Bool}) -> {List.append(&2, Dl.B, Dl.emit(ps, e, p), DocLines.lines.EndBytes(e)) == DocLines.lines.Each(DocLines.lines.Texts(p <> ps), DocLines.lines.EndBytes(e)) : List<&2, Dl.B>}:
  match ps:
    case Nil{}:
      match p:
        case Dl.Piece{t, en}:
          match e:
            case Dl.Lf{}:
              {==}
            case Dl.CrLf{}:
              {==}
    case +q <> +more:
      match p:
        case Dl.Piece{+t, en}:
          match en:
            case None{}:
              pko.chain(t, e, q, more, pko.emit(more, q, e, h))
            case Some{f}:
              match f:
                case Dl.Lf{}:
                  match e:
                    case Dl.Lf{}:
                      pko.chain(t, Dl.Lf{}, q, more, pko.emit(more, q, Dl.Lf{}, h))
                    case Dl.CrLf{}:
                      LA.pdl.absurd({List.append(&2, Dl.B, Dl.emit(q <> more, Dl.CrLf{}, Dl.Piece{t, Some{Dl.Lf{}}}), DocLines.lines.EndBytes(Dl.CrLf{})) == DocLines.lines.Each(DocLines.lines.Texts(Dl.Piece{t, Some{Dl.Lf{}}} <> (q <> more)), DocLines.lines.EndBytes(Dl.CrLf{})) : List<&2, Dl.B>}, Equal.sym(Bool, False{}, True{}, h))
                case Dl.CrLf{}:
                  match e:
                    case Dl.Lf{}:
                      LA.pdl.absurd({List.append(&2, Dl.B, Dl.emit(q <> more, Dl.Lf{}, Dl.Piece{t, Some{Dl.CrLf{}}}), DocLines.lines.EndBytes(Dl.Lf{})) == DocLines.lines.Each(DocLines.lines.Texts(Dl.Piece{t, Some{Dl.CrLf{}}} <> (q <> more)), DocLines.lines.EndBytes(Dl.Lf{})) : List<&2, Dl.B>}, Equal.sym(Bool, False{}, True{}, h))
                    case Dl.CrLf{}:
                      pko.chain(t, Dl.CrLf{}, q, more, pko.emit(more, q, Dl.CrLf{}, h))

def DocLines.persist_keeps_one_ending(p, ps, e, one):
  pko.emit(ps, p, e, one)
