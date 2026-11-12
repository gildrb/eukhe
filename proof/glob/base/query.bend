# eukhe: lemmas of the proofs of the glob queries: the alternatives of a
# pattern list (compile) match a text exactly when a pattern globset
# accepts matches it (gq.pat); a search over texts is an or over them
# (gq.texts); drop on lists of texts.

import Base
import ../../../bend/glob/parse.bend as GParse
import ../../../bend/glob/items.bend as GItems
import ../../../bend/glob/match.bend as GMatch
import ../../../bend/glob/queries.bend as GQuery
import ../../../laws/glob.bend as Glob
import ./logic.bend as GL
import ./seq.bend as GS

def gq.pr(+o: GItems.Opts, res: Result<&2, &2, GParse.Err, GParse.Glob>, +rest: List<&2, List<&2, GItems.It>>, +s: String, -x: Bool, ih: {GS.gs.OL(GItems.bytes(s), rest) == x : Bool}) -> {GS.gs.OL(GItems.bytes(s), GQuery.compile.r(o, res, rest)) == Bool.or(Glob.sp_parsed_hit(o, res, s), x) : Bool}:
  match res:
    case Fail{e}:
      ih
    case Done{+g}:
      +bs = GItems.bytes(s)
      +its = GItems.items(o, g)
      %Equal.sym(Bool, GS.gs.OL(bs, List.append(&2, List<&2, GItems.It>, its, rest)), Bool.or(GS.gs.OL(bs, its), GS.gs.OL(bs, rest)), GS.gs.ol_app(bs, its, rest)) : {_ == Bool.or(GMatch.any_full(bs, its), x) : Bool}
      %Equal.sym(Bool, GMatch.any_full(bs, its), GS.gs.OL(bs, its), GS.gs.af(bs, its)) : {Bool.or(GS.gs.OL(bs, its), GS.gs.OL(bs, rest)) == Bool.or(_, x) : Bool}
      %ih : {Bool.or(GS.gs.OL(bs, its), GS.gs.OL(bs, rest)) == Bool.or(GS.gs.OL(bs, its), _) : Bool}
      {==}

# the alternatives of the patterns match s exactly when one they parse to does
def gq.pat(+o: GItems.Opts, ps: List<&2, String>, +s: String) -> {GS.gs.OL(GItems.bytes(s), GQuery.compile(o, ps)) == Glob.sp_pat_hit(o, ps, s) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> +r:
      gq.pr(o, GParse.parse(p), GQuery.compile(o, r), s, Glob.sp_pat_hit(o, r, s), gq.pat(o, r, s))

# a search over the texts is an or over them
def gq.texts(+o: GItems.Opts, +ps: List<&2, String>, ss: List<&2, String>) -> {GQuery.hit_any(ss, GQuery.compile(o, ps)) == Glob.sp_texts_hit(o, ps, ss) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +r:
      +xs = GQuery.compile(o, ps)
      +bs = GItems.bytes(s)
      %Equal.sym(Bool, GMatch.or_else(GMatch.any_full(bs, xs), u => GQuery.hit_any(r, xs)), Bool.or(GMatch.any_full(bs, xs), GQuery.hit_any(r, xs)), GS.gs.af_or(GMatch.any_full(bs, xs), GQuery.hit_any(r, xs))) : {_ == Bool.or(Glob.sp_pat_hit(o, ps, s), Glob.sp_texts_hit(o, ps, r)) : Bool}
      %Equal.sym(Bool, GMatch.any_full(bs, xs), GS.gs.OL(bs, xs), GS.gs.af(bs, xs)) : {Bool.or(_, GQuery.hit_any(r, xs)) == Bool.or(Glob.sp_pat_hit(o, ps, s), Glob.sp_texts_hit(o, ps, r)) : Bool}
      %gq.pat(o, ps, s) : {Bool.or(GS.gs.OL(bs, xs), GQuery.hit_any(r, xs)) == Bool.or(_, Glob.sp_texts_hit(o, ps, r)) : Bool}
      %gq.texts(o, ps, r) : {Bool.or(GS.gs.OL(bs, xs), GQuery.hit_any(r, xs)) == Bool.or(GS.gs.OL(bs, xs), _) : Bool}
      {==}

# Lists of texts
# --------------

def gq.drop0(ss: List<&2, String>) -> {List.drop(&2, String, ss, 0n) == ss : List<&2, String>}:
  match ss:
    case Nil{}:
      {==}
    case s <> r:
      {==}

def gq.drop_drop(ss: List<&2, String>, k: Nat, +n: Nat) -> {List.drop(&2, String, List.drop(&2, String, ss, k), n) == List.drop(&2, String, ss, Nat.add(k, n)) : List<&2, String>}:
  match ss k:
    case Nil{} k:
      match n:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case s <> r 0n:
      {==}
    case s <> r 1n+m:
      gq.drop_drop(r, m, n)
