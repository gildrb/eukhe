# eukhe: the proof of LAW glob_token_literal
#
# PROOF: a char is one item per UTF-8 byte b, the class b..b (folded with
# the fold option); unfolded, b..b holds x exactly when x == b
# (GL.gl.in_one). By induction on the char's bytes.

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/seq.bend as GS

def tl.nil(bs: List<&2, U32>) -> {Glob.sp_lang(bs, Nil{}) == List.is_empty(&2, U32, bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def tl.f(cs: List<&2, U32>, bs: List<&2, U32>) -> {Glob.sp_lang(bs, GItems.lit.go(cs, False{})) == Glob.sp_same(cs, bs) : Bool}:
  match cs:
    case Nil{}:
      tl.nil(bs)
    case +b <> r:
      match bs:
        case Nil{}:
          {==}
        case +x <> +t:
          GL.gl.and_c(GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{b, b}]}, x), U32.is_eq(x, b), Glob.sp_lang(t, GItems.lit.go(r, False{})), Glob.sp_same(r, t), GL.gl.in_one(b, x), tl.f(r, t))

def tl.t(cs: List<&2, U32>, bs: List<&2, U32>) -> {Glob.sp_lang(bs, GItems.lit.go(cs, True{})) == Glob.sp_same_fold(cs, bs) : Bool}:
  match cs:
    case Nil{}:
      tl.nil(bs)
    case +b <> r:
      match bs:
        case Nil{}:
          {==}
        case +x <> +t:
          Equal.cong(Bool, Bool, z => Bool.and(GMatch.bc(GItems.BSet{False{}, True{}, [GItems.BR{b, b}]}, x), z), Glob.sp_lang(t, GItems.lit.go(r, True{})), Glob.sp_same_fold(r, t), tl.t(r, t))

def tl.alt(+its: List<&2, GItems.It>, +bs: List<&2, U32>) -> {GS.gs.OL(bs, [its]) == Glob.sp_lang(bs, its) : Bool}:
  GL.gl.or_false(Glob.sp_lang(bs, its))

# one fold: the char's one alternative, then its items
def tl.one(+sep: Bool, +fold: Bool, +x: U32, +bs: List<&2, U32>) -> {Glob.sp_m(GItems.Opts{sep, fold}, [GParse.TLit{Chr{x}}], bs) == Glob.sp_lang(bs, GItems.lit.go(GItems.utf8(x, Nil{}), fold)) : Bool}:
  +its = GItems.lit.go(GItems.utf8(x, Nil{}), fold)
  Equal.trans(Bool, Glob.sp_m(GItems.Opts{sep, fold}, [GParse.TLit{Chr{x}}], bs), GS.gs.OL(bs, [its]), Glob.sp_lang(bs, its), GS.gs.m1(GItems.Opts{sep, fold}, GParse.TLit{Chr{x}}, bs), tl.alt(its, bs))

def tl.go(+sep: Bool, c: Char, +bs: List<&2, U32>) -> {(Glob.sp_m(GItems.Opts{sep, False{}}, [GParse.TLit{c}], bs), Glob.sp_m(GItems.Opts{sep, True{}}, [GParse.TLit{c}], bs)) == (Glob.sp_same(GItems.utf8(Char.to_u32(c), Nil{}), bs), Glob.sp_same_fold(GItems.utf8(Char.to_u32(c), Nil{}), bs)) : Bool & Bool}:
  match c:
    case Chr{+x}:
      +cs = GItems.utf8(x, Nil{})
      +m0 = Glob.sp_m(GItems.Opts{sep, False{}}, [GParse.TLit{Chr{x}}], bs)
      +m1 = Glob.sp_m(GItems.Opts{sep, True{}}, [GParse.TLit{Chr{x}}], bs)
      GL.gl.pair(m0, m1, Glob.sp_same(cs, bs), Glob.sp_same_fold(cs, bs), Equal.trans(Bool, m0, Glob.sp_lang(bs, GItems.lit.go(cs, False{})), Glob.sp_same(cs, bs), tl.one(sep, False{}, x, bs), tl.f(cs, bs)), Equal.trans(Bool, m1, Glob.sp_lang(bs, GItems.lit.go(cs, True{})), Glob.sp_same_fold(cs, bs), tl.one(sep, True{}, x, bs), tl.t(cs, bs)))

def Glob.glob_token_literal(sep, c, bs):
  tl.go(sep, c, bs)
