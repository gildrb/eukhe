# eukhe: lemmas of the proof of glob_items: the code's regex of each
# token, token list and pattern is the spec's (structure for structure).

import Base
import ../../../bend/glob.bend as G
import ../../../laws/glob.bend as Glob

def gi.lit(bs: List<&2, U32>, +fold: Bool) -> {G.lit.go(bs, fold) == Glob.sp_lit(bs, fold) : List<&2, G.It>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> r:
      %Equal.sym(List<&2, G.It>, G.lit.go(r, fold), Glob.sp_lit(r, fold), gi.lit(r, fold)) : {G.One{G.BSet{False{}, fold, [G.BR{b, b}]}} <> _ == Glob.sp_lit(b <> r, fold) : List<&2, G.It>}
      {==}

def gi.each(bs: List<&2, U32>, rest: List<&2, G.BR>) -> {G.singles(bs, rest) == Glob.sp_each(bs, rest) : List<&2, G.BR>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> r:
      %Equal.sym(List<&2, G.BR>, G.singles(r, rest), Glob.sp_each(r, rest), gi.each(r, rest)) : {G.BR{b, b} <> _ == Glob.sp_each(b <> r, rest) : List<&2, G.BR>}
      {==}

# a byte before the bytes split: one more single first
def gi.mid_cons(+b: U32, p: List<&2, U32> & U32, hb: List<&2, U32>, rest: List<&2, G.BR>) -> {G.rg.mid(G.split_last.cons(b, p), hb, rest) == G.BR{b, b} <> G.rg.mid(p, hb, rest) : List<&2, G.BR>}:
  match p hb:
    case (i, l) Nil{}:
      {==}
    case (i, l) h <> t:
      {==}

def gi.span(r: List<&2, U32>, +b: U32, +hb: List<&2, U32>, +rest: List<&2, G.BR>) -> {G.rg.mid(G.split_last(r, b), hb, rest) == Glob.sp_span(r, b, hb, rest) : List<&2, G.BR>}:
  match r:
    case Nil{}:
      match hb:
        case Nil{}:
          {==}
        case h <> t:
          %Equal.sym(List<&2, G.BR>, G.singles(t, rest), Glob.sp_each(t, rest), gi.each(t, rest)) : {G.BR{b, h} <> _ == Glob.sp_span(Nil{}, b, h <> t, rest) : List<&2, G.BR>}
          {==}
    case +c <> +t:
      %Equal.sym(List<&2, G.BR>, G.rg.mid(G.split_last.cons(b, G.split_last(t, c)), hb, rest), G.BR{b, b} <> G.rg.mid(G.split_last(t, c), hb, rest), gi.mid_cons(b, G.split_last(t, c), hb, rest)) : {_ == Glob.sp_span(c <> t, b, hb, rest) : List<&2, G.BR>}
      %Equal.sym(List<&2, G.BR>, G.rg.mid(G.split_last(t, c), hb, rest), Glob.sp_span(t, c, hb, rest), gi.span(t, c, hb, rest)) : {G.BR{b, b} <> _ == Glob.sp_span(c <> t, b, hb, rest) : List<&2, G.BR>}
      {==}

def gi.multi(bs: List<&2, U32>, +hi: U32, +rest: List<&2, G.BR>) -> {G.rg.multi(bs, hi, rest) == Glob.sp_range.k(bs, G.utf8(hi, Nil{}), rest) : List<&2, G.BR>}:
  match bs:
    case Nil{}:
      {==}
    case b <> r:
      gi.span(r, b, G.utf8(hi, Nil{}), rest)

def gi.rg(same: Bool, +lo: U32, +hi: U32, +rest: List<&2, G.BR>) -> {G.rg.k(lo, hi, rest, same) == Glob.sp_range.same(same, lo, hi, rest) : List<&2, G.BR>}:
  match same:
    case True{}:
      gi.each(G.utf8(lo, Nil{}), rest)
    case False{}:
      gi.multi(G.utf8(lo, Nil{}), hi, rest)

def gi.rgs(rs: List<&2, G.Rg>) -> {G.rgs(rs) == Glob.sp_ranges(rs) : List<&2, G.BR>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case G.Rg{+lo, +hi}:
          %Equal.sym(List<&2, G.BR>, G.rgs(t), Glob.sp_ranges(t), gi.rgs(t)) : {G.rg.k(G.code(lo), G.code(hi), _, U32.is_eq(G.code(lo), G.code(hi))) == Glob.sp_ranges(G.Rg{lo, hi} <> t) : List<&2, G.BR>}
          gi.rg(U32.is_eq(G.code(lo), G.code(hi)), G.code(lo), G.code(hi), Glob.sp_ranges(t))

def gi.any(sep: Bool, fold: Bool) -> {G.tok(G.Opts{sep, fold}, G.TAny{}) == Glob.sp_tok(G.Opts{sep, fold}, G.TAny{}) : List<&2, List<&2, G.It>>}:
  match sep:
    case True{}:
      {==}
    case False{}:
      {==}

def gi.star(sep: Bool, fold: Bool) -> {G.tok(G.Opts{sep, fold}, G.TZom{}) == Glob.sp_tok(G.Opts{sep, fold}, G.TZom{}) : List<&2, List<&2, G.It>>}:
  match sep:
    case True{}:
      {==}
    case False{}:
      {==}

def gi.tok(o: G.Opts, t: G.Tok) -> {G.tok(o, t) == Glob.sp_tok(o, t) : List<&2, List<&2, G.It>>}:
  match o:
    case G.Opts{+sep, +fold}:
      match t:
        case G.TLit{c}:
          %Equal.sym(List<&2, G.It>, G.lit.go(G.utf8(G.code(c), Nil{}), fold), Glob.sp_lit(G.utf8(G.code(c), Nil{}), fold), gi.lit(G.utf8(G.code(c), Nil{}), fold)) : {[_] == Glob.sp_tok(G.Opts{sep, fold}, G.TLit{c}) : List<&2, List<&2, G.It>>}
          {==}
        case G.TAny{}:
          gi.any(sep, fold)
        case G.TZom{}:
          gi.star(sep, fold)
        case G.TRPre{}:
          {==}
        case G.TRSuf{}:
          {==}
        case G.TRZom{}:
          {==}
        case G.TCls{neg, rs}:
          %Equal.sym(List<&2, G.BR>, G.rgs(rs), Glob.sp_ranges(rs), gi.rgs(rs)) : {[[G.One{G.BSet{neg, fold, _}}]] == Glob.sp_tok(G.Opts{sep, fold}, G.TCls{neg, rs}) : List<&2, List<&2, G.It>>}
          {==}

def gi.pre(+a: List<&2, G.It>, bs: List<&2, List<&2, G.It>>) -> {G.seq.pre(a, bs) == Glob.sp_then(a, bs) : List<&2, List<&2, G.It>>}:
  match bs:
    case Nil{}:
      {==}
    case b <> r:
      %Equal.sym(List<&2, List<&2, G.It>>, G.seq.pre(a, r), Glob.sp_then(a, r), gi.pre(a, r)) : {List.append(&2, G.It, a, b) <> _ == Glob.sp_then(a, b <> r) : List<&2, List<&2, G.It>>}
      {==}

def gi.cross(as: List<&2, List<&2, G.It>>, +bs: List<&2, List<&2, G.It>>) -> {G.seq.cross(as, bs) == Glob.sp_prod(as, bs) : List<&2, List<&2, G.It>>}:
  match as:
    case Nil{}:
      {==}
    case +a <> r:
      %Equal.sym(List<&2, List<&2, G.It>>, G.seq.pre(a, bs), Glob.sp_then(a, bs), gi.pre(a, bs)) : {List.append(&2, List<&2, G.It>, _, G.seq.cross(r, bs)) == Glob.sp_prod(a <> r, bs) : List<&2, List<&2, G.It>>}
      %Equal.sym(List<&2, List<&2, G.It>>, G.seq.cross(r, bs), Glob.sp_prod(r, bs), gi.cross(r, bs)) : {List.append(&2, List<&2, G.It>, Glob.sp_then(a, bs), _) == Glob.sp_prod(a <> r, bs) : List<&2, List<&2, G.It>>}
      {==}

def gi.seq(+o: G.Opts, ts: List<&2, G.Tok>) -> {G.seq(o, ts) == Glob.sp_seq(o, ts) : List<&2, List<&2, G.It>>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      %Equal.sym(List<&2, List<&2, G.It>>, G.tok(o, t), Glob.sp_tok(o, t), gi.tok(o, t)) : {G.seq.cross(_, G.seq(o, r)) == Glob.sp_seq(o, t <> r) : List<&2, List<&2, G.It>>}
      %Equal.sym(List<&2, List<&2, G.It>>, G.seq(o, r), Glob.sp_seq(o, r), gi.seq(o, r)) : {G.seq.cross(Glob.sp_tok(o, t), _) == Glob.sp_seq(o, t <> r) : List<&2, List<&2, G.It>>}
      gi.cross(Glob.sp_tok(o, t), Glob.sp_seq(o, r))

def gi.alts(+o: G.Opts, xs: List<&2, List<&2, G.Tok>>) -> {G.alts(o, xs) == Glob.sp_alts(o, xs) : List<&2, List<&2, G.It>>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> r:
      %Equal.sym(List<&2, List<&2, G.It>>, G.seq(o, a), Glob.sp_seq(o, a), gi.seq(o, a)) : {List.append(&2, List<&2, G.It>, _, G.alts(o, r)) == Glob.sp_alts(o, a <> r) : List<&2, List<&2, G.It>>}
      %Equal.sym(List<&2, List<&2, G.It>>, G.alts(o, r), Glob.sp_alts(o, r), gi.alts(o, r)) : {List.append(&2, List<&2, G.It>, Glob.sp_seq(o, a), _) == Glob.sp_alts(o, a <> r) : List<&2, List<&2, G.It>>}
      {==}

# the code's regex of a parsed pattern is the spec's
def gi.items(+o: G.Opts, g: G.Glob) -> {G.items(o, g) == Glob.sp_items(o, g) : List<&2, List<&2, G.It>>}:
  match g:
    case G.Glob{xs, solo}:
      match solo:
        case True{}:
          {==}
        case False{}:
          gi.alts(o, xs)
