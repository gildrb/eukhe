# eukhe: the proof of LAW glob_token_recursive
#
# PROOF: per token, its alternatives (GS.gs.m1) over the bytes: `/` is
# the class 47..47, which is x == 47 (GL.gl.in_one); a star of any byte
# then `/` matches the bytes that end with `/` (tr.ends); the rest is
# Bool algebra per shape of the bytes (empty, one byte, more).

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/seq.bend as GS
import ./glob_match_branches.bend as PMB

# the class of `/` holds x exactly when x is 47
def tr.e(+x: U32) -> {GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x) == U32.is_eq(x, 47) : Bool}:
  GL.gl.in_one(47, x)

def tr.and_c(-a: Bool, -b: Bool, -c: Bool, -d: Bool, ab: {a == b : Bool}, cd: {c == d : Bool}) -> {Bool.and(a, c) == Bool.and(b, d) : Bool}:
  %ab : {Bool.and(a, c) == Bool.and(_, d) : Bool}
  %cd : {Bool.and(a, c) == Bool.and(a, _) : Bool}
  {==}

# a star of any byte, then `/`: the bytes end with `/`
def tr.ends(bs: List<&2, U32>) -> {Glob.sp_lang(bs, [GItems.Star{GItems.BAny{}}, GItems.slash()]) == Glob.sp_slash_last(bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          +b = GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x)
          %Equal.sym(Bool, b, U32.is_eq(x, 47), tr.e(x)) : {Bool.or(Bool.and(_, True{}), False{}) == U32.is_eq(x, 47) : Bool}
          %Equal.sym(Bool, Bool.and(U32.is_eq(x, 47), True{}), U32.is_eq(x, 47), GL.gl.and_true(U32.is_eq(x, 47))) : {Bool.or(_, False{}) == U32.is_eq(x, 47) : Bool}
          GL.gl.or_false(U32.is_eq(x, 47))
        case +y <> +u:
          +b = GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x)
          %Equal.sym(Bool, Bool.and(b, False{}), False{}, GL.gl.and_false(b)) : {Bool.or(_, Glob.sp_lang(y <> u, [GItems.Star{GItems.BAny{}}, GItems.slash()])) == Glob.sp_slash_last(y <> u) : Bool}
          tr.ends(y <> u)

def tr.pre_b(e: Bool) -> {Bool.or(Bool.and(e, True{}), Bool.or(e, False{})) == e : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def tr.pre_m(b: Bool, s: Bool) -> {Bool.or(Bool.and(b, False{}), Bool.or(s, False{})) == s : Bool}:
  match b s:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# `**/`: the empty bytes, or bytes that end with `/`
def tr.pre(bs: List<&2, U32>) -> {GS.gs.OL(bs, [Nil{}, [GItems.slash()], [GItems.Star{GItems.BAny{}}, GItems.slash()]]) == Bool.or(List.is_empty(&2, U32, bs), Glob.sp_slash_last(bs)) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          +b = GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x)
          %Equal.sym(Bool, Glob.sp_lang([x], [GItems.Star{GItems.BAny{}}, GItems.slash()]), U32.is_eq(x, 47), tr.ends([x])) : {Bool.or(Bool.and(b, True{}), Bool.or(_, False{})) == U32.is_eq(x, 47) : Bool}
          %Equal.sym(Bool, b, U32.is_eq(x, 47), tr.e(x)) : {Bool.or(Bool.and(_, True{}), Bool.or(U32.is_eq(x, 47), False{})) == U32.is_eq(x, 47) : Bool}
          tr.pre_b(U32.is_eq(x, 47))
        case +y <> +u:
          +b = GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x)
          %Equal.sym(Bool, Glob.sp_lang(x <> y <> u, [GItems.Star{GItems.BAny{}}, GItems.slash()]), Glob.sp_slash_last(y <> u), tr.ends(x <> y <> u)) : {Bool.or(Bool.and(b, False{}), Bool.or(_, False{})) == Glob.sp_slash_last(y <> u) : Bool}
          tr.pre_m(b, Glob.sp_slash_last(y <> u))

# `/**`: bytes that start with `/`
def tr.suf(bs: List<&2, U32>) -> {GS.gs.OL(bs, [[GItems.slash(), GItems.Star{GItems.BAny{}}]]) == Glob.sp_slash_first(bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +x <> +t:
      +b = GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x)
      %Equal.sym(Bool, Glob.sp_lang(t, [GItems.Star{GItems.BAny{}}]), True{}, PMB.mbr.star(t)) : {Bool.or(Bool.and(b, _), False{}) == U32.is_eq(x, 47) : Bool}
      %Equal.sym(Bool, Bool.and(b, True{}), b, GL.gl.and_true(b)) : {Bool.or(_, False{}) == U32.is_eq(x, 47) : Bool}
      %Equal.sym(Bool, Bool.or(b, False{}), b, GL.gl.or_false(b)) : {_ == U32.is_eq(x, 47) : Bool}
      tr.e(x)

def tr.tup3(-a: Bool, -b: Bool, -c: Bool, -d: Bool, -e: Bool, -f: Bool, ad: {a == d : Bool}, be: {b == e : Bool}, cf: {c == f : Bool}) -> {(a, b, c) == (d, e, f) : Bool & Bool & Bool}:
  %ad : {(a, b, c) == (_, e, f) : Bool & Bool & Bool}
  %be : {(a, b, c) == (a, _, f) : Bool & Bool & Bool}
  %cf : {(a, b, c) == (a, b, _) : Bool & Bool & Bool}
  {==}

def tr.zom_b(e: Bool) -> {Bool.or(Bool.and(e, True{}), Bool.or(Bool.and(e, False{}), False{})) == Bool.and(e, e) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def tr.zom_m(b: Bool, p: Bool) -> {Bool.or(Bool.and(b, False{}), Bool.or(Bool.and(b, p), False{})) == Bool.and(b, p) : Bool}:
  match b p:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# `/**/`: bytes that start and end with `/`
def tr.zom(bs: List<&2, U32>) -> {GS.gs.OL(bs, [[GItems.slash()], [GItems.slash(), GItems.Star{GItems.BAny{}}, GItems.slash()]]) == Bool.and(Glob.sp_slash_first(bs), Glob.sp_slash_last(bs)) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          +b = GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x)
          %Equal.sym(Bool, b, U32.is_eq(x, 47), tr.e(x)) : {Bool.or(Bool.and(_, True{}), Bool.or(Bool.and(_, False{}), False{})) == Bool.and(U32.is_eq(x, 47), U32.is_eq(x, 47)) : Bool}
          tr.zom_b(U32.is_eq(x, 47))
        case +y <> +u:
          +b = GMatch.bc(GItems.BSet{False{}, False{}, [GItems.BR{47, 47}]}, x)
          +p = Glob.sp_lang(y <> u, [GItems.Star{GItems.BAny{}}, GItems.slash()])
          Equal.trans(Bool, Bool.or(Bool.and(b, False{}), Bool.or(Bool.and(b, p), False{})), Bool.and(b, p), Bool.and(U32.is_eq(x, 47), Glob.sp_slash_last(y <> u)), tr.zom_m(b, p), tr.and_c(b, U32.is_eq(x, 47), p, Glob.sp_slash_last(y <> u), tr.e(x), tr.ends(y <> u)))

def tr.all(o: GItems.Opts, +bs: List<&2, U32>) -> {(GS.gs.OL(bs, GItems.tok(o, GParse.TRPre{})), GS.gs.OL(bs, GItems.tok(o, GParse.TRSuf{})), GS.gs.OL(bs, GItems.tok(o, GParse.TRZom{}))) == (Bool.or(List.is_empty(&2, U32, bs), Glob.sp_slash_last(bs)), Glob.sp_slash_first(bs), Bool.and(Glob.sp_slash_first(bs), Glob.sp_slash_last(bs))) : Bool & Bool & Bool}:
  match o:
    case GItems.Opts{sep, fold}:
      tr.tup3(GS.gs.OL(bs, GItems.tok(GItems.Opts{sep, fold}, GParse.TRPre{})), GS.gs.OL(bs, GItems.tok(GItems.Opts{sep, fold}, GParse.TRSuf{})), GS.gs.OL(bs, GItems.tok(GItems.Opts{sep, fold}, GParse.TRZom{})), Bool.or(List.is_empty(&2, U32, bs), Glob.sp_slash_last(bs)), Glob.sp_slash_first(bs), Bool.and(Glob.sp_slash_first(bs), Glob.sp_slash_last(bs)), tr.pre(bs), tr.suf(bs), tr.zom(bs))

def Glob.glob_token_recursive(o, bs):
  Equal.trans(Bool & Bool & Bool, (Glob.sp_m(o, [GParse.TRPre{}], bs), Glob.sp_m(o, [GParse.TRSuf{}], bs), Glob.sp_m(o, [GParse.TRZom{}], bs)), (GS.gs.OL(bs, GItems.tok(o, GParse.TRPre{})), GS.gs.OL(bs, GItems.tok(o, GParse.TRSuf{})), GS.gs.OL(bs, GItems.tok(o, GParse.TRZom{}))), (Bool.or(List.is_empty(&2, U32, bs), Glob.sp_slash_last(bs)), Glob.sp_slash_first(bs), Bool.and(Glob.sp_slash_first(bs), Glob.sp_slash_last(bs))), tr.tup3(Glob.sp_m(o, [GParse.TRPre{}], bs), Glob.sp_m(o, [GParse.TRSuf{}], bs), Glob.sp_m(o, [GParse.TRZom{}], bs), GS.gs.OL(bs, GItems.tok(o, GParse.TRPre{})), GS.gs.OL(bs, GItems.tok(o, GParse.TRSuf{})), GS.gs.OL(bs, GItems.tok(o, GParse.TRZom{})), GS.gs.m1(o, GParse.TRPre{}, bs), GS.gs.m1(o, GParse.TRSuf{}, bs), GS.gs.m1(o, GParse.TRZom{}, bs)), tr.all(o, bs))
