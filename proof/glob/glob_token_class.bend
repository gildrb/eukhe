# eukhe: the proof of LAW glob_token_class
#
# PROOF: a class is one item, one byte of its byte class (GS.gs.m1 for the
# alternatives); per shape of the bytes.

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/seq.bend as GS

def tc.one(+k: GItems.BC, bs: List<&2, U32>) -> {GS.gs.OL(bs, [[GItems.One{k}]]) == Glob.sp_one_of(k, bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +x <> t:
      match t:
        case Nil{}:
          GL.gl.or_false(Bool.and(GMatch.bc(k, x), True{}))
        case y <> u:
          GL.gl.or_false(Bool.and(GMatch.bc(k, x), False{}))

def Glob.glob_token_class(sep, fold, neg, rs, bs):
  +k = {GItems.BSet{neg, fold, GItems.rgs(rs)} : GItems.BC}
  Equal.trans(Bool, Glob.sp_m(GItems.Opts{sep, fold}, [GParse.TCls{neg, rs}], bs), GS.gs.OL(bs, [[GItems.One{k}]]), Glob.sp_one_of(k, bs), GS.gs.m1(GItems.Opts{sep, fold}, GParse.TCls{neg, rs}, bs), tc.one(k, bs))
