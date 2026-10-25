# eukhe: lemmas of the proof of glob_items: the code's regex of each
# token, token list and pattern is the spec's (structure for structure).

import Base
import ../../../bend/glob/parse.bend as GParse
import ../../../bend/glob/items.bend as GItems
import ../../../laws/glob.bend as Glob

def gi.lit(bs: List<&2, U32>, +fold: Bool) -> {GItems.lit.go(bs, fold) == Glob.sp_lit(bs, fold) : List<&2, GItems.It>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> r:
      %Equal.sym(List<&2, GItems.It>, GItems.lit.go(r, fold), Glob.sp_lit(r, fold), gi.lit(r, fold)) : {GItems.One{GItems.BSet{False{}, fold, [GItems.BR{b, b}]}} <> _ == Glob.sp_lit(b <> r, fold) : List<&2, GItems.It>}
      {==}

def gi.each(bs: List<&2, U32>, rest: List<&2, GItems.BR>) -> {GItems.singles(bs, rest) == Glob.sp_each(bs, rest) : List<&2, GItems.BR>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> r:
      %Equal.sym(List<&2, GItems.BR>, GItems.singles(r, rest), Glob.sp_each(r, rest), gi.each(r, rest)) : {GItems.BR{b, b} <> _ == Glob.sp_each(b <> r, rest) : List<&2, GItems.BR>}
      {==}

# a byte before the bytes split: one more single first
def gi.mid_cons(+b: U32, p: List<&2, U32> & U32, hb: List<&2, U32>, rest: List<&2, GItems.BR>) -> {GItems.rg.mid(GItems.split_last.cons(b, p), hb, rest) == GItems.BR{b, b} <> GItems.rg.mid(p, hb, rest) : List<&2, GItems.BR>}:
  match p hb:
    case (i, l) Nil{}:
      {==}
    case (i, l) h <> t:
      {==}

def gi.span(r: List<&2, U32>, +b: U32, +hb: List<&2, U32>, +rest: List<&2, GItems.BR>) -> {GItems.rg.mid(GItems.split_last(r, b), hb, rest) == Glob.sp_span(r, b, hb, rest) : List<&2, GItems.BR>}:
  match r:
    case Nil{}:
      match hb:
        case Nil{}:
          {==}
        case h <> t:
          %Equal.sym(List<&2, GItems.BR>, GItems.singles(t, rest), Glob.sp_each(t, rest), gi.each(t, rest)) : {GItems.BR{b, h} <> _ == Glob.sp_span(Nil{}, b, h <> t, rest) : List<&2, GItems.BR>}
          {==}
    case +c <> +t:
      %Equal.sym(List<&2, GItems.BR>, GItems.rg.mid(GItems.split_last.cons(b, GItems.split_last(t, c)), hb, rest), GItems.BR{b, b} <> GItems.rg.mid(GItems.split_last(t, c), hb, rest), gi.mid_cons(b, GItems.split_last(t, c), hb, rest)) : {_ == Glob.sp_span(c <> t, b, hb, rest) : List<&2, GItems.BR>}
      %Equal.sym(List<&2, GItems.BR>, GItems.rg.mid(GItems.split_last(t, c), hb, rest), Glob.sp_span(t, c, hb, rest), gi.span(t, c, hb, rest)) : {GItems.BR{b, b} <> _ == Glob.sp_span(c <> t, b, hb, rest) : List<&2, GItems.BR>}
      {==}

def gi.multi(bs: List<&2, U32>, +hi: U32, +rest: List<&2, GItems.BR>) -> {GItems.rg.multi(bs, hi, rest) == Glob.sp_range.k(bs, GItems.utf8(hi, Nil{}), rest) : List<&2, GItems.BR>}:
  match bs:
    case Nil{}:
      {==}
    case b <> r:
      gi.span(r, b, GItems.utf8(hi, Nil{}), rest)

def gi.rg(same: Bool, +lo: U32, +hi: U32, +rest: List<&2, GItems.BR>) -> {GItems.rg.k(lo, hi, rest, same) == Glob.sp_range.same(same, lo, hi, rest) : List<&2, GItems.BR>}:
  match same:
    case True{}:
      gi.each(GItems.utf8(lo, Nil{}), rest)
    case False{}:
      gi.multi(GItems.utf8(lo, Nil{}), hi, rest)

def gi.rgs(rs: List<&2, GParse.Rg>) -> {GItems.rgs(rs) == Glob.sp_ranges(rs) : List<&2, GItems.BR>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case GParse.Rg{+lo, +hi}:
          %Equal.sym(List<&2, GItems.BR>, GItems.rgs(t), Glob.sp_ranges(t), gi.rgs(t)) : {GItems.rg.k(GParse.code(lo), GParse.code(hi), _, U32.is_eq(GParse.code(lo), GParse.code(hi))) == Glob.sp_ranges(GParse.Rg{lo, hi} <> t) : List<&2, GItems.BR>}
          gi.rg(U32.is_eq(GParse.code(lo), GParse.code(hi)), GParse.code(lo), GParse.code(hi), Glob.sp_ranges(t))

def gi.any(sep: Bool, fold: Bool) -> {GItems.tok(GItems.Opts{sep, fold}, GParse.TAny{}) == Glob.sp_tok(GItems.Opts{sep, fold}, GParse.TAny{}) : List<&2, List<&2, GItems.It>>}:
  match sep:
    case True{}:
      {==}
    case False{}:
      {==}

def gi.star(sep: Bool, fold: Bool) -> {GItems.tok(GItems.Opts{sep, fold}, GParse.TZom{}) == Glob.sp_tok(GItems.Opts{sep, fold}, GParse.TZom{}) : List<&2, List<&2, GItems.It>>}:
  match sep:
    case True{}:
      {==}
    case False{}:
      {==}

def gi.tok(o: GItems.Opts, t: GParse.Tok) -> {GItems.tok(o, t) == Glob.sp_tok(o, t) : List<&2, List<&2, GItems.It>>}:
  match o:
    case GItems.Opts{+sep, +fold}:
      match t:
        case GParse.TLit{c}:
          %Equal.sym(List<&2, GItems.It>, GItems.lit.go(GItems.utf8(GParse.code(c), Nil{}), fold), Glob.sp_lit(GItems.utf8(GParse.code(c), Nil{}), fold), gi.lit(GItems.utf8(GParse.code(c), Nil{}), fold)) : {[_] == Glob.sp_tok(GItems.Opts{sep, fold}, GParse.TLit{c}) : List<&2, List<&2, GItems.It>>}
          {==}
        case GParse.TAny{}:
          gi.any(sep, fold)
        case GParse.TZom{}:
          gi.star(sep, fold)
        case GParse.TRPre{}:
          {==}
        case GParse.TRSuf{}:
          {==}
        case GParse.TRZom{}:
          {==}
        case GParse.TCls{neg, rs}:
          %Equal.sym(List<&2, GItems.BR>, GItems.rgs(rs), Glob.sp_ranges(rs), gi.rgs(rs)) : {[[GItems.One{GItems.BSet{neg, fold, _}}]] == Glob.sp_tok(GItems.Opts{sep, fold}, GParse.TCls{neg, rs}) : List<&2, List<&2, GItems.It>>}
          {==}

def gi.pre(+a: List<&2, GItems.It>, bs: List<&2, List<&2, GItems.It>>) -> {GItems.seq.pre(a, bs) == Glob.sp_then(a, bs) : List<&2, List<&2, GItems.It>>}:
  match bs:
    case Nil{}:
      {==}
    case b <> r:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.seq.pre(a, r), Glob.sp_then(a, r), gi.pre(a, r)) : {List.append(&2, GItems.It, a, b) <> _ == Glob.sp_then(a, b <> r) : List<&2, List<&2, GItems.It>>}
      {==}

def gi.cross(as: List<&2, List<&2, GItems.It>>, +bs: List<&2, List<&2, GItems.It>>) -> {GItems.seq.cross(as, bs) == Glob.sp_prod(as, bs) : List<&2, List<&2, GItems.It>>}:
  match as:
    case Nil{}:
      {==}
    case +a <> r:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.seq.pre(a, bs), Glob.sp_then(a, bs), gi.pre(a, bs)) : {List.append(&2, List<&2, GItems.It>, _, GItems.seq.cross(r, bs)) == Glob.sp_prod(a <> r, bs) : List<&2, List<&2, GItems.It>>}
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.seq.cross(r, bs), Glob.sp_prod(r, bs), gi.cross(r, bs)) : {List.append(&2, List<&2, GItems.It>, Glob.sp_then(a, bs), _) == Glob.sp_prod(a <> r, bs) : List<&2, List<&2, GItems.It>>}
      {==}

def gi.seq(+o: GItems.Opts, ts: List<&2, GParse.Tok>) -> {GItems.seq(o, ts) == Glob.sp_seq(o, ts) : List<&2, List<&2, GItems.It>>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.tok(o, t), Glob.sp_tok(o, t), gi.tok(o, t)) : {GItems.seq.cross(_, GItems.seq(o, r)) == Glob.sp_seq(o, t <> r) : List<&2, List<&2, GItems.It>>}
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.seq(o, r), Glob.sp_seq(o, r), gi.seq(o, r)) : {GItems.seq.cross(Glob.sp_tok(o, t), _) == Glob.sp_seq(o, t <> r) : List<&2, List<&2, GItems.It>>}
      gi.cross(Glob.sp_tok(o, t), Glob.sp_seq(o, r))

def gi.alts(+o: GItems.Opts, xs: List<&2, List<&2, GParse.Tok>>) -> {GItems.alts(o, xs) == Glob.sp_alts(o, xs) : List<&2, List<&2, GItems.It>>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> r:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.seq(o, a), Glob.sp_seq(o, a), gi.seq(o, a)) : {List.append(&2, List<&2, GItems.It>, _, GItems.alts(o, r)) == Glob.sp_alts(o, a <> r) : List<&2, List<&2, GItems.It>>}
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.alts(o, r), Glob.sp_alts(o, r), gi.alts(o, r)) : {List.append(&2, List<&2, GItems.It>, Glob.sp_seq(o, a), _) == Glob.sp_alts(o, a <> r) : List<&2, List<&2, GItems.It>>}
      {==}

# the code's regex of a parsed pattern is the spec's
def gi.items(+o: GItems.Opts, g: GParse.Glob) -> {GItems.items(o, g) == Glob.sp_items(o, g) : List<&2, List<&2, GItems.It>>}:
  match g:
    case GParse.Glob{xs, solo}:
      match solo:
        case True{}:
          {==}
        case False{}:
          gi.alts(o, xs)
