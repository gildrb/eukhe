# eukhe: lemmas of the proofs of glob_matches, glob_groups and
# glob_allowed: the code's searches over alternatives, texts, groups and
# patterns are the spec's, from the matcher (GB.gb.full) and the regex
# (GI.gi.items).

import Base
import ../../../bend/glob/parse.bend as GParse
import ../../../bend/glob/items.bend as GItems
import ../../../bend/glob/match.bend as GMatch
import ../../../bend/glob/queries.bend as GQuery
import ../../../laws/glob.bend as Glob
import ./match.bend as GB
import ./items.bend as GI

def gq.any_or(b: Bool, +bs: List<&2, U32>, r: List<&2, List<&2, GItems.It>>, ih: {GMatch.any_full(bs, r) == Glob.sp_any(bs, r) : Bool}) -> {GMatch.or_else(b, u => GMatch.any_full(bs, r)) == Bool.or(b, Glob.sp_any(bs, r)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a search over alternatives is the spec's
def gq.any(+bs: List<&2, U32>, xs: List<&2, List<&2, GItems.It>>) -> {GMatch.any_full(bs, xs) == Glob.sp_any(bs, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +r:
      %Equal.sym(Bool, GMatch.full(bs, a), Glob.sp_lang(bs, a), GB.gb.full(bs, a)) : {GMatch.or_else(_, u => GMatch.any_full(bs, r)) == Glob.sp_any(bs, a <> r) : Bool}
      gq.any_or(Glob.sp_lang(bs, a), bs, r, gq.any(bs, r))

# a pattern's match is the spec's
def gq.matches(+o: GItems.Opts, +g: GParse.Glob, +s: String) -> {GMatch.matches(o, g, s) == Glob.sp_any(GItems.bytes(s), Glob.sp_items(o, g)) : Bool}:
  %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.items(o, g), Glob.sp_items(o, g), GI.gi.items(o, g)) : {GMatch.any_full(GItems.bytes(s), _) == Glob.sp_any(GItems.bytes(s), Glob.sp_items(o, g)) : Bool}
  gq.any(GItems.bytes(s), Glob.sp_items(o, g))

def gq.compile.r(+o: GItems.Opts, r: Result<&2, &2, GParse.Err, GParse.Glob>, rest: List<&2, List<&2, GItems.It>>) -> {GQuery.compile.r(o, r, rest) == Glob.sp_compile.r(o, r, rest) : List<&2, List<&2, GItems.It>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+g}:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GItems.items(o, g), Glob.sp_items(o, g), GI.gi.items(o, g)) : {List.append(&2, List<&2, GItems.It>, _, rest) == Glob.sp_compile.r(o, Done{g}, rest) : List<&2, List<&2, GItems.It>>}
      {==}

# the alternatives of a pattern list are the spec's
def gq.compile(+o: GItems.Opts, ps: List<&2, String>) -> {GQuery.compile(o, ps) == Glob.sp_compile(o, ps) : List<&2, List<&2, GItems.It>>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +r:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GQuery.compile(o, r), Glob.sp_compile(o, r), gq.compile(o, r)) : {GQuery.compile.r(o, GParse.parse(p), _) == Glob.sp_compile(o, p <> r) : List<&2, List<&2, GItems.It>>}
      gq.compile.r(o, GParse.parse(p), Glob.sp_compile(o, r))

def gq.hit_or(b: Bool, r: List<&2, String>, +xs: List<&2, List<&2, GItems.It>>, ih: {GQuery.hit_any(r, xs) == Glob.sp_hit(r, xs) : Bool}) -> {GMatch.or_else(b, u => GQuery.hit_any(r, xs)) == Bool.or(b, Glob.sp_hit(r, xs)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a search over texts is the spec's
def gq.hit(ss: List<&2, String>, +xs: List<&2, List<&2, GItems.It>>) -> {GQuery.hit_any(ss, xs) == Glob.sp_hit(ss, xs) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +r:
      %Equal.sym(Bool, GMatch.any_full(GItems.bytes(s), xs), Glob.sp_any(GItems.bytes(s), xs), gq.any(GItems.bytes(s), xs)) : {GMatch.or_else(_, u => GQuery.hit_any(r, xs)) == Glob.sp_hit(s <> r, xs) : Bool}
      gq.hit_or(Glob.sp_any(GItems.bytes(s), xs), r, xs, gq.hit(r, xs))

# the groups are the spec's
def gq.groups(ks: List<&2, Nat>, +xs: List<&2, List<&2, GItems.It>>, +ss: List<&2, String>) -> {GQuery.groups(ks, xs, ss) == Glob.sp_groups(ks, xs, ss) : List<&2, Bool>}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +r:
      %Equal.sym(Bool, GQuery.hit_any(List.take(&2, String, ss, k), xs), Glob.sp_hit(List.take(&2, String, ss, k), xs), gq.hit(List.take(&2, String, ss, k), xs)) : {_ <> GQuery.groups(r, xs, List.drop(&2, String, ss, k)) == Glob.sp_groups(k <> r, xs, ss) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, GQuery.groups(r, xs, List.drop(&2, String, ss, k)), Glob.sp_groups(r, xs, List.drop(&2, String, ss, k)), gq.groups(r, xs, List.drop(&2, String, ss, k))) : {Glob.sp_hit(List.take(&2, String, ss, k), xs) <> _ == Glob.sp_groups(k <> r, xs, ss) : List<&2, Bool>}
      {==}
