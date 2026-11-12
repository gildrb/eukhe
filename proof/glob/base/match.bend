# eukhe: lemmas shared by the proofs of area glob. The matcher's table
# (G.rows) holds, for each suffix of the items, the spec's answer
# (gb.row_spec): by induction on the text, then the items, as the table
# is built. Each rewrite names its equation; `%e : P` takes e : {new ==
# old}.

import Base
import ../../../bend/glob/items.bend as GItems
import ../../../bend/glob/match.bend as GMatch
import ../../../laws/glob.bend as Glob

# The table
# ---------

# the spec's answer for each suffix of the items (the whole list first)
def gb.row_spec(+bs: List<&2, U32>, its: List<&2, GItems.It>) -> List<&2, Bool>:
  match its:
    case Nil{}:
      [Glob.sp_lang(bs, Nil{})]
    case i <> +k:
      Glob.sp_lang(bs, i <> k) <> gb.row_spec(bs, k)

def gb.hd_row(+bs: List<&2, U32>, its: List<&2, GItems.It>) -> {GMatch.hd(gb.row_spec(bs, its)) == Glob.sp_lang(bs, its) : Bool}:
  match its:
    case Nil{}:
      {==}
    case i <> k:
      {==}

# the row of the empty text is the spec's
def gb.nul(its: List<&2, GItems.It>) -> {GMatch.nul(its) == gb.row_spec(Nil{}, its) : List<&2, Bool>}:
  match its:
    case Nil{}:
      {==}
    case i <> +k:
      match i:
        case GItems.One{c}:
          %Equal.sym(List<&2, Bool>, GMatch.nul(k), gb.row_spec(Nil{}, k), gb.nul(k)) : {False{} <> _ == gb.row_spec(Nil{}, GItems.One{c} <> k) : List<&2, Bool>}
          {==}
        case GItems.Star{c}:
          %Equal.sym(List<&2, Bool>, GMatch.nul(k), gb.row_spec(Nil{}, k), gb.nul(k)) : {GMatch.hd(_) <> _ == gb.row_spec(Nil{}, GItems.Star{c} <> k) : List<&2, Bool>}
          %Equal.sym(Bool, GMatch.hd(gb.row_spec(Nil{}, k)), Glob.sp_lang(Nil{}, k), gb.hd_row(Nil{}, k)) : {_ <> gb.row_spec(Nil{}, k) == gb.row_spec(Nil{}, GItems.Star{c} <> k) : List<&2, Bool>}
          {==}

def gb.row.cons(i: GItems.It, +x: U32, +t: List<&2, U32>, +k: List<&2, GItems.It>) -> {GMatch.row.cons(i, x, Glob.sp_lang(t, i <> k), gb.row_spec(t, k), gb.row_spec(x <> t, k)) == gb.row_spec(x <> t, i <> k) : List<&2, Bool>}:
  match i:
    case GItems.One{+c}:
      %Equal.sym(Bool, GMatch.hd(gb.row_spec(t, k)), Glob.sp_lang(t, k), gb.hd_row(t, k)) : {Bool.and(GMatch.bc(c, x), _) <> gb.row_spec(x <> t, k) == gb.row_spec(x <> t, GItems.One{c} <> k) : List<&2, Bool>}
      {==}
    case GItems.Star{+c}:
      %Equal.sym(Bool, GMatch.hd(gb.row_spec(x <> t, k)), Glob.sp_lang(x <> t, k), gb.hd_row(x <> t, k)) : {Bool.or(_, Bool.and(GMatch.bc(c, x), Glob.sp_lang(t, GItems.Star{c} <> k))) <> gb.row_spec(x <> t, k) == gb.row_spec(x <> t, GItems.Star{c} <> k) : List<&2, Bool>}
      {==}

# one more byte: the row of x <> t from the spec's row of t
def gb.row(its: List<&2, GItems.It>, +x: U32, +t: List<&2, U32>) -> {GMatch.row(its, x, gb.row_spec(t, its)) == gb.row_spec(x <> t, its) : List<&2, Bool>}:
  match its:
    case Nil{}:
      {==}
    case i <> +k:
      %Equal.sym(List<&2, Bool>, GMatch.row(k, x, gb.row_spec(t, k)), gb.row_spec(x <> t, k), gb.row(k, x, t)) : {GMatch.row.cons(i, x, Glob.sp_lang(t, i <> k), gb.row_spec(t, k), _) == gb.row_spec(x <> t, i <> k) : List<&2, Bool>}
      gb.row.cons(i, x, t, k)

# the whole table is the spec's
def gb.rows(bs: List<&2, U32>, +its: List<&2, GItems.It>) -> {GMatch.rows(bs, its) == gb.row_spec(bs, its) : List<&2, Bool>}:
  match bs:
    case Nil{}:
      gb.nul(its)
    case +x <> +t:
      %Equal.sym(List<&2, Bool>, GMatch.rows(t, its), gb.row_spec(t, its), gb.rows(t, its)) : {GMatch.row(its, x, _) == gb.row_spec(x <> t, its) : List<&2, Bool>}
      gb.row(its, x, t)

# the matcher is the spec
def gb.full(+bs: List<&2, U32>, +its: List<&2, GItems.It>) -> {GMatch.full(bs, its) == Glob.sp_lang(bs, its) : Bool}:
  %Equal.sym(List<&2, Bool>, GMatch.rows(bs, its), gb.row_spec(bs, its), gb.rows(bs, its)) : {GMatch.hd(_) == Glob.sp_lang(bs, its) : Bool}
  gb.hd_row(bs, its)
