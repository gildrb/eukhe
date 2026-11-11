# eukhe: the proof of LAW edit_writes_new_lines

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

# the texts of appended pieces are the appended texts
def ewn.app(ps: List<&2, Dl.Piece>, +qs: List<&2, Dl.Piece>) -> {DocLines.lines.Texts(List.append(&2, Dl.Piece, ps, qs)) == List.append(&2, List<&2, Dl.B>, DocLines.lines.Texts(ps), DocLines.lines.Texts(qs)) : List<&2, List<&2, Dl.B>>}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Dl.Piece{t, en}:
          %ewn.app(rest, qs) : {t <> DocLines.lines.Texts(List.append(&2, Dl.Piece, rest, qs)) == t <> _ : List<&2, List<&2, Dl.B>>}
          {==}

# the texts of the first n pieces are the first n texts
def ewn.take(ps: List<&2, Dl.Piece>, n: Nat) -> {DocLines.lines.Texts(List.take(&2, Dl.Piece, ps, n)) == List.take(&2, List<&2, Dl.B>, DocLines.lines.Texts(ps), n) : List<&2, List<&2, Dl.B>>}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Dl.Piece{t, en}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              %ewn.take(rest, m) : {t <> DocLines.lines.Texts(List.take(&2, Dl.Piece, rest, m)) == t <> _ : List<&2, List<&2, Dl.B>>}
              {==}

# the texts after the first n pieces are the texts after the first n
def ewn.drop(ps: List<&2, Dl.Piece>, n: Nat) -> {DocLines.lines.Texts(List.drop(&2, Dl.Piece, ps, n)) == List.drop(&2, List<&2, Dl.B>, DocLines.lines.Texts(ps), n) : List<&2, List<&2, Dl.B>>}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match p:
        case Dl.Piece{t, en}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              ewn.drop(rest, m)

# the texts of new pieces are the new lines
def ewn.fresh(xs: List<&2, List<&2, Dl.B>>) -> {DocLines.lines.Texts(Dl.fresh(xs)) == xs : List<&2, List<&2, Dl.B>>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      %ewn.fresh(rest) : {x <> DocLines.lines.Texts(Dl.fresh(rest)) == x <> _ : List<&2, List<&2, Dl.B>>}
      {==}

def DocLines.edit_writes_new_lines(bom, bs, s, k, xs):
  +ps = Dl.pieces(Dl.split(bs))
  %ewn.take(ps, s) : {DocLines.lines.EdTexts(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == List.append(&2, List<&2, Dl.B>, _, List.append(&2, List<&2, Dl.B>, xs, List.drop(&2, List<&2, Dl.B>, DocLines.lines.Texts(ps), Nat.add(s, k)))) : List<&2, List<&2, Dl.B>>}
  %ewn.drop(ps, Nat.add(s, k)) : {DocLines.lines.EdTexts(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == List.append(&2, List<&2, Dl.B>, DocLines.lines.Texts(List.take(&2, Dl.Piece, ps, s)), List.append(&2, List<&2, Dl.B>, xs, _)) : List<&2, List<&2, Dl.B>>}
  %ewn.fresh(xs) : {DocLines.lines.EdTexts(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == List.append(&2, List<&2, Dl.B>, DocLines.lines.Texts(List.take(&2, Dl.Piece, ps, s)), List.append(&2, List<&2, Dl.B>, _, DocLines.lines.Texts(List.drop(&2, Dl.Piece, ps, Nat.add(s, k))))) : List<&2, List<&2, Dl.B>>}
  %ewn.app(Dl.fresh(xs), List.drop(&2, Dl.Piece, ps, Nat.add(s, k))) : {DocLines.lines.EdTexts(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == List.append(&2, List<&2, Dl.B>, DocLines.lines.Texts(List.take(&2, Dl.Piece, ps, s)), _) : List<&2, List<&2, Dl.B>>}
  ewn.app(List.take(&2, Dl.Piece, ps, s), List.append(&2, Dl.Piece, Dl.fresh(xs), List.drop(&2, Dl.Piece, ps, Nat.add(s, k))))
