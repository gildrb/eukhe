# eukhe: lemmas the proofs of area doc_lines share

import Base
import ../../bend/doc_lines.bend as Dl

# ---- doc_lines ----

# proof_doc_lines: the line laws of LAWS.bend section documents (F4): a file
# loaded and persisted is the same bytes; an edit keeps every byte outside
# the lines it replaces; grep and read show the same rows.

# Logic and lists
# ---------------

def pdl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pdl.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pdl.BD(_, Unit, A)
  Unit{}

# Lines: the proof-side views
# ---------------------------

# the bytes of the lines
def pdl.cat(ls: Dl.Lines) -> List<&2, Dl.B>:
  match ls:
    case Dl.More{t, e, r}:
      List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), pdl.cat(r)))
    case Dl.Last{t}:
      t

# Load and persist
# ----------------

# a byte put before the body puts it before the bytes of its lines
def pdl.cons_cat(b: Dl.B, ls: Dl.Lines) -> {pdl.cat(Dl.cons(b, ls)) == b <> pdl.cat(ls) : List<&2, Dl.B>}:
  match b:
    case Dl.A{}:
      match ls:
        case Dl.More{t, e, r}:
          {==}
        case Dl.Last{t}:
          {==}
    case Dl.N{}:
      {==}
    case Dl.R{}:
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

# the lines of a body are its bytes
def pdl.split_cat(bs: List<&2, Dl.B>) -> {pdl.cat(Dl.split(bs)) == bs : List<&2, Dl.B>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      %Equal.sym(List<&2, Dl.B>, pdl.cat(Dl.cons(b, Dl.split(rest))), b <> pdl.cat(Dl.split(rest)), pdl.cons_cat(b, Dl.split(rest))) : {_ == b <> rest : List<&2, Dl.B>}
      %pdl.split_cat(rest) : {b <> pdl.cat(Dl.split(rest)) == b <> _ : List<&2, Dl.B>}
      {==}

def pdl.emit_more(+t: List<&2, Dl.B>, +e: Dl.End, r: Dl.Lines, +c: Dl.End, ih: {pdl.cat(r) == Dl.start(Dl.pieces(r), e) : List<&2, Dl.B>}) -> {pdl.cat(Dl.More{t, e, r}) == Dl.start(Dl.pieces(Dl.More{t, e, r}), c) : List<&2, Dl.B>}:
  match r:
    case Dl.Last{t2}:
      {==}
    case Dl.More{+t2, +e2, +r2}:
      %Equal.sym(List<&2, Dl.B>, pdl.cat(Dl.More{t2, e2, r2}), Dl.start(Dl.pieces(Dl.More{t2, e2, r2}), e), ih) : {List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(e), _)) == Dl.start(Dl.pieces(Dl.More{t, e, Dl.More{t2, e2, r2}}), c) : List<&2, Dl.B>}
      {==}

# the lines of a loaded file persist as their bytes, with any carry
def pdl.start_cat(ls: Dl.Lines, +c: Dl.End) -> {pdl.cat(ls) == Dl.start(Dl.pieces(ls), c) : List<&2, Dl.B>}:
  match ls:
    case Dl.More{+t, +e, +r}:
      pdl.emit_more(t, e, r, c, pdl.start_cat(r, e))
    case Dl.Last{t}:
      {==}
