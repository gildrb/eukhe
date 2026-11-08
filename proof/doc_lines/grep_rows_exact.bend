# eukhe: the proof of LAW grep_rows_exact: grep's split, terminator strip
# and last-row cut step alike with the spec's rows, byte by byte

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./base.bend as LA
import ./grep_line_is_read_line.bend as PG

def glr.push(+b: Dl.B, rs: List<&2, List<&2, Dl.B>>) -> {DocLines.lines.Push(b, rs) == Dl.pushN(b, rs) : List<&2, List<&2, Dl.B>>}:
  match rs:
    case Nil{}:
      {==}
    case q <> m:
      {==}

# the lines of one piece at least are one line at least
def glr.lines_ne(ps: List<&2, List<&2, Dl.B>>, h: {List.is_empty(&2, List<&2, Dl.B>, ps) == False{} : Bool}) -> {List.is_empty(&2, List<&2, Dl.B>, Dl.lines(ps)) == False{} : Bool}:
  match ps:
    case Nil{}:
      LA.pdl.absurd({List.is_empty(&2, List<&2, Dl.B>, Dl.lines(Nil{})) == False{} : Bool}, h)
    case q <> m:
      match m:
        case Nil{}:
          {==}
        case q2 <> m2:
          {==}

# a `\r` that a `\n` ends is stripped with it
def glr.drop_r(ps: List<&2, List<&2, Dl.B>>, h: {List.is_empty(&2, List<&2, Dl.B>, ps) == False{} : Bool}) -> {Dl.lines(Nil{} <> ps) == Dl.lines([Dl.R{}] <> ps) : List<&2, List<&2, Dl.B>>}:
  match ps:
    case Nil{}:
      LA.pdl.absurd({Dl.lines(Nil{} <> Nil{}) == Dl.lines([Dl.R{}] <> Nil{}) : List<&2, List<&2, Dl.B>>}, h)
    case q <> m:
      {==}

# rs, grep's rows of c <> more, give grep's rows of `\r` <> c <> more
def glr.after_r(+c: Dl.B, +more: List<&2, Dl.B>, rs: List<&2, List<&2, Dl.B>>, ih: {rs == Dl.lastrow(Dl.lines(Dl.splitN(c <> more))) : List<&2, List<&2, Dl.B>>}) -> {DocLines.lines.AfterR(c, rs) == Dl.lastrow(Dl.lines(Dl.splitN(Dl.R{} <> c <> more))) : List<&2, List<&2, Dl.B>>}:
  match c:
    case Dl.N{}:
      %glr.drop_r(Dl.splitN(more), PG.pdl.split_ne(more)) : {rs == Dl.lastrow(_) : List<&2, List<&2, Dl.B>>}
      ih
    case Dl.A{}:
      %PG.pdl.lines_pushR(Dl.A{}, Dl.splitN(more)) : {DocLines.lines.Push(Dl.R{}, rs) == Dl.lastrow(_) : List<&2, List<&2, Dl.B>>}
      %PG.pdl.lr_step(Dl.R{}, Dl.lines(Dl.splitN(Dl.A{} <> more)), glr.lines_ne(Dl.splitN(Dl.A{} <> more), PG.pdl.split_ne(Dl.A{} <> more))) : {DocLines.lines.Push(Dl.R{}, rs) == _ : List<&2, List<&2, Dl.B>>}
      %ih : {DocLines.lines.Push(Dl.R{}, rs) == Dl.pushN(Dl.R{}, _) : List<&2, List<&2, Dl.B>>}
      glr.push(Dl.R{}, rs)
    case Dl.R{}:
      %PG.pdl.lines_pushR(Dl.R{}, Dl.splitN(more)) : {DocLines.lines.Push(Dl.R{}, rs) == Dl.lastrow(_) : List<&2, List<&2, Dl.B>>}
      %PG.pdl.lr_step(Dl.R{}, Dl.lines(Dl.splitN(Dl.R{} <> more)), glr.lines_ne(Dl.splitN(Dl.R{} <> more), PG.pdl.split_ne(Dl.R{} <> more))) : {DocLines.lines.Push(Dl.R{}, rs) == _ : List<&2, List<&2, Dl.B>>}
      %ih : {DocLines.lines.Push(Dl.R{}, rs) == Dl.pushN(Dl.R{}, _) : List<&2, List<&2, Dl.B>>}
      glr.push(Dl.R{}, rs)

# the spec's rows of y <> t are grep's
def glr.rows(t: List<&2, Dl.B>, +y: Dl.B) -> {DocLines.lines.Rows(t, y) == Dl.lastrow(Dl.lines(Dl.splitN(y <> t))) : List<&2, List<&2, Dl.B>>}:
  match t:
    case Nil{}:
      match y:
        case Dl.A{}:
          {==}
        case Dl.R{}:
          {==}
        case Dl.N{}:
          {==}
    case +c <> +more:
      match y:
        case Dl.A{}:
          %PG.pdl.lines_pushA(Dl.splitN(c <> more)) : {DocLines.lines.Push(Dl.A{}, DocLines.lines.Rows(more, c)) == Dl.lastrow(_) : List<&2, List<&2, Dl.B>>}
          %PG.pdl.lr_step(Dl.A{}, Dl.lines(Dl.splitN(c <> more)), glr.lines_ne(Dl.splitN(c <> more), PG.pdl.split_ne(c <> more))) : {DocLines.lines.Push(Dl.A{}, DocLines.lines.Rows(more, c)) == _ : List<&2, List<&2, Dl.B>>}
          %glr.rows(more, c) : {DocLines.lines.Push(Dl.A{}, DocLines.lines.Rows(more, c)) == Dl.pushN(Dl.A{}, _) : List<&2, List<&2, Dl.B>>}
          glr.push(Dl.A{}, DocLines.lines.Rows(more, c))
        case Dl.N{}:
          %PG.pdl.lines_x([], Dl.splitN(c <> more), PG.pdl.split_ne(c <> more)) : {Nil{} <> DocLines.lines.Rows(more, c) == Dl.lastrow(_) : List<&2, List<&2, Dl.B>>}
          %PG.pdl.lr_step(Dl.N{}, Dl.lines(Dl.splitN(c <> more)), glr.lines_ne(Dl.splitN(c <> more), PG.pdl.split_ne(c <> more))) : {Nil{} <> DocLines.lines.Rows(more, c) == _ : List<&2, List<&2, Dl.B>>}
          %glr.rows(more, c) : {Nil{} <> DocLines.lines.Rows(more, c) == Nil{} <> _ : List<&2, List<&2, Dl.B>>}
          {==}
        case Dl.R{}:
          glr.after_r(c, more, DocLines.lines.Rows(more, c), glr.rows(more, c))

def DocLines.grep_rows_exact(bs):
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      Equal.sym(List<&2, List<&2, Dl.B>>, DocLines.lines.Rows(rest, b), Dl.lastrow(Dl.lines(Dl.splitN(b <> rest))), glr.rows(rest, b))
