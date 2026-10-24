# eukhe: lemmas about the projection of a file's lines (bend/doc_lines.bend
# `proj`) that the proofs of areas doc_lines and doc_rows share

import Base
import ../../../bend/doc_lines.bend as Dl
import ../../../laws/doc_rows.bend as DocRows

# the texts of lines (the texts of load's pieces, in order)
def dlp.texts(ls: Dl.Lines) -> List<&2, List<&2, Dl.B>>:
  match ls:
    case Dl.More{t, e, r}:
      t <> dlp.texts(r)
    case Dl.Last{t}:
      [t]

# the lengths of the projected lines are the lengths of the texts
def dlp.lens(ls: Dl.Lines) -> {DocRows.rows.Lens(Dl.proj.lines(Dl.pieces(ls))) == DocRows.rows.LensB(dlp.texts(ls)) : List<&2, Nat>}:
  match ls:
    case Dl.More{t, e, r}:
      %dlp.lens(r) : {List.length(&2, Dl.B, t) <> DocRows.rows.Lens(Dl.proj.lines(Dl.pieces(r))) == List.length(&2, Dl.B, t) <> _ : List<&2, Nat>}
      {==}
    case Dl.Last{t}:
      {==}

# a content byte put before lines goes into the first text
def dlp.texts_a(ls: Dl.Lines) -> {dlp.texts(Dl.push(Dl.A{}, ls)) == Dl.pushN(Dl.A{}, dlp.texts(ls)) : List<&2, List<&2, Dl.B>>}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

# a `\r` before a content byte is content of the first text
def dlp.texts_ra(ls: Dl.Lines) -> {dlp.texts(Dl.cons(Dl.R{}, Dl.push(Dl.A{}, ls))) == Dl.pushN(Dl.R{}, Dl.pushN(Dl.A{}, dlp.texts(ls))) : List<&2, List<&2, Dl.B>>}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

# a `\r` before a `\r` is content of the first text
def dlp.texts_rr(ls: Dl.Lines) -> {dlp.texts(Dl.cons(Dl.R{}, Dl.cons(Dl.R{}, ls))) == Dl.pushN(Dl.R{}, dlp.texts(Dl.cons(Dl.R{}, ls))) : List<&2, List<&2, Dl.B>>}:
  match ls:
    case Dl.More{t, e, r}:
      match t:
        case Nil{}:
          match e:
            case Dl.Lf{}:
              {==}
            case Dl.CrLf{}:
              {==}
        case h <> tt:
          {==}
    case Dl.Last{t}:
      {==}

# the texts of the lines of a body (after a pending `\r` when p) are the
# pieces of its normalized text
def dlp.texts_nm(bs: List<&2, Dl.B>, p: Bool) -> {dlp.texts(Dl.split(Dl.lead(p, bs))) == Dl.splitN(Dl.nm(bs, p)) : List<&2, List<&2, Dl.B>>}:
  match bs:
    case Nil{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          match p:
            case True{}:
              %dlp.texts_nm(rest, False{}) : {dlp.texts(Dl.cons(Dl.R{}, Dl.push(Dl.A{}, Dl.split(rest)))) == Dl.pushN(Dl.R{}, Dl.pushN(Dl.A{}, _)) : List<&2, List<&2, Dl.B>>}
              dlp.texts_ra(Dl.split(rest))
            case False{}:
              %dlp.texts_nm(rest, False{}) : {dlp.texts(Dl.push(Dl.A{}, Dl.split(rest))) == Dl.pushN(Dl.A{}, _) : List<&2, List<&2, Dl.B>>}
              dlp.texts_a(Dl.split(rest))
        case Dl.R{}:
          match p:
            case True{}:
              %dlp.texts_nm(rest, True{}) : {dlp.texts(Dl.cons(Dl.R{}, Dl.cons(Dl.R{}, Dl.split(rest)))) == Dl.pushN(Dl.R{}, _) : List<&2, List<&2, Dl.B>>}
              dlp.texts_rr(Dl.split(rest))
            case False{}:
              dlp.texts_nm(rest, True{})
        case Dl.N{}:
          match p:
            case True{}:
              %dlp.texts_nm(rest, False{}) : {Nil{} <> dlp.texts(Dl.split(rest)) == Nil{} <> _ : List<&2, List<&2, Dl.B>>}
              {==}
            case False{}:
              %dlp.texts_nm(rest, False{}) : {Nil{} <> dlp.texts(Dl.split(rest)) == Nil{} <> _ : List<&2, List<&2, Dl.B>>}
              {==}

# the lengths of the lines Rust scans are the lengths of the pieces of the
# normalized text
def dlp.raw(+bs: List<&2, Dl.B>) -> {DocRows.rows.Lens(DocRows.rows.Pieces(bs)) == DocRows.rows.LensB(Dl.splitN(Dl.norm(bs))) : List<&2, Nat>}:
  %dlp.texts_nm(bs, False{}) : {DocRows.rows.Lens(DocRows.rows.Pieces(bs)) == DocRows.rows.LensB(_) : List<&2, Nat>}
  dlp.lens(Dl.split(bs))
