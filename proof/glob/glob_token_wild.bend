# eukhe: the proof of LAW glob_token_wild
#
# PROOF: `?` is one byte of the class `[^/]` (literal_separator) or `.`,
# `*` a run of that class (GS.gs.m1 for the alternatives); per shape of
# the bytes.

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/seq.bend as GS

def tw.one(sep: Bool, bs: List<&2, U32>) -> {GS.gs.OL(bs, [[GItems.one_or_star(sep, False{})]]) == Glob.sp_one_free(sep, bs) : Bool}:
  match sep bs:
    case True{} Nil{}:
      {==}
    case True{} +x <> t:
      match t:
        case Nil{}:
          GL.gl.or_false(Bool.and(Bool.not(U32.is_eq(x, 47)), True{}))
        case y <> u:
          GL.gl.or_false(Bool.and(Bool.not(U32.is_eq(x, 47)), False{}))
    case False{} Nil{}:
      {==}
    case False{} x <> t:
      match t:
        case Nil{}:
          {==}
        case y <> u:
          {==}

def tw.run_t(bs: List<&2, U32>) -> {Glob.sp_lang(bs, [GItems.Star{GItems.BNotSl{}}]) == Glob.sp_all_free(True{}, bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.cong(Bool, Bool, z => Bool.and(Bool.not(U32.is_eq(x, 47)), z), Glob.sp_lang(t, [GItems.Star{GItems.BNotSl{}}]), Glob.sp_all_free(True{}, t), tw.run_t(t))

def tw.run_f(bs: List<&2, U32>) -> {Glob.sp_lang(bs, [GItems.Star{GItems.BAny{}}]) == Glob.sp_all_free(False{}, bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case x <> t:
      tw.run_f(t)

def tw.star(sep: Bool, +bs: List<&2, U32>) -> {GS.gs.OL(bs, [[GItems.one_or_star(sep, True{})]]) == Glob.sp_all_free(sep, bs) : Bool}:
  match sep:
    case True{}:
      %Equal.sym(Bool, Bool.or(Glob.sp_lang(bs, [GItems.Star{GItems.BNotSl{}}]), False{}), Glob.sp_lang(bs, [GItems.Star{GItems.BNotSl{}}]), GL.gl.or_false(Glob.sp_lang(bs, [GItems.Star{GItems.BNotSl{}}]))) : {_ == Glob.sp_all_free(True{}, bs) : Bool}
      tw.run_t(bs)
    case False{}:
      %Equal.sym(Bool, Bool.or(Glob.sp_lang(bs, [GItems.Star{GItems.BAny{}}]), False{}), Glob.sp_lang(bs, [GItems.Star{GItems.BAny{}}]), GL.gl.or_false(Glob.sp_lang(bs, [GItems.Star{GItems.BAny{}}]))) : {_ == Glob.sp_all_free(False{}, bs) : Bool}
      tw.run_f(bs)

def Glob.glob_token_wild(sep, fold, bs):
  +o = {GItems.Opts{sep, fold} : GItems.Opts}
  GL.gl.pair(Glob.sp_m(o, [GParse.TAny{}], bs), Glob.sp_m(o, [GParse.TZom{}], bs), Glob.sp_one_free(sep, bs), Glob.sp_all_free(sep, bs), Equal.trans(Bool, Glob.sp_m(o, [GParse.TAny{}], bs), GS.gs.OL(bs, [[GItems.one_or_star(sep, False{})]]), Glob.sp_one_free(sep, bs), GS.gs.m1(o, GParse.TAny{}, bs), tw.one(sep, bs)), Equal.trans(Bool, Glob.sp_m(o, [GParse.TZom{}], bs), GS.gs.OL(bs, [[GItems.one_or_star(sep, True{})]]), Glob.sp_all_free(sep, bs), GS.gs.m1(o, GParse.TZom{}, bs), tw.star(sep, bs)))
