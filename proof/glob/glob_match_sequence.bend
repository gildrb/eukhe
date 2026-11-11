# eukhe: the proof of LAW glob_match_sequence
#
# PROOF: a branch's alternatives are the products of its first token's
# alternatives with those of the rest (seq.cross); the products match
# exactly the splits (GS.gs.cross, from the concatenation of items,
# GS.gs.cat); each side of a split is the token alone, or the rest alone
# (GS.gs.m1, GS.gs.m). The empty branch's one alternative is no item.

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../laws/glob.bend as Glob
import ./base/seq.bend as GS

def msq.split(+o: GItems.Opts, +t: GParse.Tok, +ts: List<&2, GParse.Tok>, +bs: List<&2, U32>, i: Nat) -> {Glob.sp_split(o, t, ts, bs, i) == GS.gs.SX(GItems.tok(o, t), GItems.seq(o, ts), bs, i) : Bool}:
  match i:
    case 0n:
      +xs = GItems.tok(o, t)
      +ys = GItems.seq(o, ts)
      %Equal.sym(Bool, Glob.sp_m(o, [t], Nil{}), GS.gs.OL(Nil{}, xs), GS.gs.m1(o, t, Nil{})) : {Bool.and(_, Glob.sp_m(o, ts, bs)) == GS.gs.SX(xs, ys, bs, 0n) : Bool}
      %Equal.sym(Bool, Glob.sp_m(o, ts, bs), GS.gs.OL(bs, ys), GS.gs.m(o, ts, bs)) : {Bool.and(GS.gs.OL(Nil{}, xs), _) == GS.gs.SX(xs, ys, bs, 0n) : Bool}
      {==}
    case 1n++j:
      +xs = GItems.tok(o, t)
      +ys = GItems.seq(o, ts)
      +tk = List.take(&2, U32, bs, 1n+j)
      +dr = List.drop(&2, U32, bs, 1n+j)
      %Equal.sym(Bool, Glob.sp_m(o, [t], tk), GS.gs.OL(tk, xs), GS.gs.m1(o, t, tk)) : {Bool.or(Bool.and(_, Glob.sp_m(o, ts, dr)), Glob.sp_split(o, t, ts, bs, j)) == GS.gs.SX(xs, ys, bs, 1n+j) : Bool}
      %Equal.sym(Bool, Glob.sp_m(o, ts, dr), GS.gs.OL(dr, ys), GS.gs.m(o, ts, dr)) : {Bool.or(Bool.and(GS.gs.OL(tk, xs), _), Glob.sp_split(o, t, ts, bs, j)) == GS.gs.SX(xs, ys, bs, 1n+j) : Bool}
      %Equal.sym(Bool, Glob.sp_split(o, t, ts, bs, j), GS.gs.SX(xs, ys, bs, j), msq.split(o, t, ts, bs, j)) : {Bool.or(Bool.and(GS.gs.OL(tk, xs), GS.gs.OL(dr, ys)), _) == GS.gs.SX(xs, ys, bs, 1n+j) : Bool}
      {==}

def msq.empty(+o: GItems.Opts, bs: List<&2, U32>) -> {Glob.sp_m(o, Nil{}, bs) == List.is_empty(&2, U32, bs) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def msq.cons(+o: GItems.Opts, +t: GParse.Tok, +ts: List<&2, GParse.Tok>, +bs: List<&2, U32>) -> {Glob.sp_m(o, t <> ts, bs) == Glob.sp_split(o, t, ts, bs, List.length(&2, U32, bs)) : Bool}:
  +n = List.length(&2, U32, bs)
  +xs = GItems.tok(o, t)
  +ys = GItems.seq(o, ts)
  +sp = Glob.sp_split(o, t, ts, bs, n)
  +ol = GS.gs.OL(bs, GItems.seq.cross(xs, ys))
  +sx = GS.gs.SX(xs, ys, bs, n)
  Equal.trans(Bool, Glob.sp_m(o, t <> ts, bs), ol, sp, GS.gs.m(o, t <> ts, bs), Equal.trans(Bool, ol, sx, sp, GS.gs.cross(xs, ys, bs), Equal.sym(Bool, sp, sx, msq.split(o, t, ts, bs, n))))

def Glob.glob_match_sequence(o, t, ts, bs):
  %Equal.sym(Bool, Glob.sp_m(o, Nil{}, bs), List.is_empty(&2, U32, bs), msq.empty(o, bs)) : {(_, Glob.sp_m(o, t <> ts, bs)) == (List.is_empty(&2, U32, bs), Glob.sp_split(o, t, ts, bs, List.length(&2, U32, bs))) : Bool & Bool}
  %Equal.sym(Bool, Glob.sp_m(o, t <> ts, bs), Glob.sp_split(o, t, ts, bs, List.length(&2, U32, bs)), msq.cons(o, t, ts, bs)) : {(List.is_empty(&2, U32, bs), _) == (List.is_empty(&2, U32, bs), Glob.sp_split(o, t, ts, bs, List.length(&2, U32, bs))) : Bool & Bool}
  {==}
