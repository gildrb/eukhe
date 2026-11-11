# eukhe: the proof of LAW glob_match_branches
#
# PROOF: a pattern's alternatives are its branches' alternatives one after
# the other (alts), and a search over appended alternatives is the or of
# the two searches (GS.gs.ol_app); a branch's search is sp_m (GS.gs.m).
# The lone `**` is one star of any byte, which matches every byte text.

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../bend/glob/match.bend as GMatch
import ../../laws/glob.bend as Glob
import ./base/seq.bend as GS

def mbr.go(+o: GItems.Opts, xs: List<&2, List<&2, GParse.Tok>>, +bs: List<&2, U32>) -> {GS.gs.OL(bs, GItems.alts(o, xs)) == Glob.sp_branches(o, xs, bs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +ts <> +r:
      +ols = GS.gs.OL(bs, GItems.seq(o, ts))
      +olr = GS.gs.OL(bs, GItems.alts(o, r))
      %Equal.sym(Bool, GS.gs.OL(bs, List.append(&2, List<&2, GItems.It>, GItems.seq(o, ts), GItems.alts(o, r))), Bool.or(ols, olr), GS.gs.ol_app(bs, GItems.seq(o, ts), GItems.alts(o, r))) : {_ == Bool.or(Glob.sp_m(o, ts, bs), Glob.sp_branches(o, r, bs)) : Bool}
      %Equal.sym(Bool, Glob.sp_m(o, ts, bs), ols, GS.gs.m(o, ts, bs)) : {Bool.or(ols, olr) == Bool.or(_, Glob.sp_branches(o, r, bs)) : Bool}
      %mbr.go(o, r, bs) : {Bool.or(ols, olr) == Bool.or(ols, _) : Bool}
      {==}

# a star of any byte matches every byte text
def mbr.star(bs: List<&2, U32>) -> {Glob.sp_lang(bs, [GItems.Star{GItems.BAny{}}]) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case x <> t:
      mbr.star(t)

def mbr.solo(+bs: List<&2, U32>) -> {GMatch.any_full(bs, [[GItems.Star{GItems.BAny{}}]]) == True{} : Bool}:
  +xs = {[[GItems.Star{GItems.BAny{}}]] : List<&2, List<&2, GItems.It>>}
  %Equal.sym(Bool, GMatch.any_full(bs, xs), GS.gs.OL(bs, xs), GS.gs.af(bs, xs)) : {_ == True{} : Bool}
  %Equal.sym(Bool, Glob.sp_lang(bs, [GItems.Star{GItems.BAny{}}]), True{}, mbr.star(bs)) : {Bool.or(_, False{}) == True{} : Bool}
  {==}

def Glob.glob_match_branches(o, xs, s):
  +bs = GItems.bytes(s)
  (Equal.trans(Bool, GMatch.any_full(bs, GItems.alts(o, xs)), GS.gs.OL(bs, GItems.alts(o, xs)), Glob.sp_branches(o, xs, bs), GS.gs.af(bs, GItems.alts(o, xs)), mbr.go(o, xs, bs)), mbr.solo(bs))
