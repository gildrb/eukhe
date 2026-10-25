# eukhe: lemmas of the proofs of glob_matches, glob_groups and
# glob_allowed: the code's searches over alternatives, texts, groups and
# patterns are the spec's, from the matcher (GB.gb.full) and the regex
# (GI.gi.items).

import Base
import ../../../bend/glob.bend as G
import ../../../laws/glob.bend as Glob
import ./match.bend as GB
import ./items.bend as GI

def gq.any_or(b: Bool, +bs: List<&2, U32>, r: List<&2, List<&2, G.It>>, ih: {G.any_full(bs, r) == Glob.sp_any(bs, r) : Bool}) -> {G.or_else(b, u => G.any_full(bs, r)) == Bool.or(b, Glob.sp_any(bs, r)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a search over alternatives is the spec's
def gq.any(+bs: List<&2, U32>, xs: List<&2, List<&2, G.It>>) -> {G.any_full(bs, xs) == Glob.sp_any(bs, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +r:
      %Equal.sym(Bool, G.full(bs, a), Glob.sp_lang(bs, a), GB.gb.full(bs, a)) : {G.or_else(_, u => G.any_full(bs, r)) == Glob.sp_any(bs, a <> r) : Bool}
      gq.any_or(Glob.sp_lang(bs, a), bs, r, gq.any(bs, r))

# a pattern's match is the spec's
def gq.matches(+o: G.Opts, +g: G.Glob, +s: String) -> {G.matches(o, g, s) == Glob.sp_any(G.bytes(s), Glob.sp_items(o, g)) : Bool}:
  %Equal.sym(List<&2, List<&2, G.It>>, G.items(o, g), Glob.sp_items(o, g), GI.gi.items(o, g)) : {G.any_full(G.bytes(s), _) == Glob.sp_any(G.bytes(s), Glob.sp_items(o, g)) : Bool}
  gq.any(G.bytes(s), Glob.sp_items(o, g))

def gq.compile.r(+o: G.Opts, r: Result<&2, &2, G.Err, G.Glob>, rest: List<&2, List<&2, G.It>>) -> {G.compile.r(o, r, rest) == Glob.sp_compile.r(o, r, rest) : List<&2, List<&2, G.It>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+g}:
      %Equal.sym(List<&2, List<&2, G.It>>, G.items(o, g), Glob.sp_items(o, g), GI.gi.items(o, g)) : {List.append(&2, List<&2, G.It>, _, rest) == Glob.sp_compile.r(o, Done{g}, rest) : List<&2, List<&2, G.It>>}
      {==}

# the alternatives of a pattern list are the spec's
def gq.compile(+o: G.Opts, ps: List<&2, String>) -> {G.compile(o, ps) == Glob.sp_compile(o, ps) : List<&2, List<&2, G.It>>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +r:
      %Equal.sym(List<&2, List<&2, G.It>>, G.compile(o, r), Glob.sp_compile(o, r), gq.compile(o, r)) : {G.compile.r(o, G.parse(p), _) == Glob.sp_compile(o, p <> r) : List<&2, List<&2, G.It>>}
      gq.compile.r(o, G.parse(p), Glob.sp_compile(o, r))

def gq.hit_or(b: Bool, r: List<&2, String>, +xs: List<&2, List<&2, G.It>>, ih: {G.hit_any(r, xs) == Glob.sp_hit(r, xs) : Bool}) -> {G.or_else(b, u => G.hit_any(r, xs)) == Bool.or(b, Glob.sp_hit(r, xs)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a search over texts is the spec's
def gq.hit(ss: List<&2, String>, +xs: List<&2, List<&2, G.It>>) -> {G.hit_any(ss, xs) == Glob.sp_hit(ss, xs) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +r:
      %Equal.sym(Bool, G.any_full(G.bytes(s), xs), Glob.sp_any(G.bytes(s), xs), gq.any(G.bytes(s), xs)) : {G.or_else(_, u => G.hit_any(r, xs)) == Glob.sp_hit(s <> r, xs) : Bool}
      gq.hit_or(Glob.sp_any(G.bytes(s), xs), r, xs, gq.hit(r, xs))

# the groups are the spec's
def gq.groups(ks: List<&2, Nat>, +xs: List<&2, List<&2, G.It>>, +ss: List<&2, String>) -> {G.groups(ks, xs, ss) == Glob.sp_groups(ks, xs, ss) : List<&2, Bool>}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +r:
      %Equal.sym(Bool, G.hit_any(List.take(&2, String, ss, k), xs), Glob.sp_hit(List.take(&2, String, ss, k), xs), gq.hit(List.take(&2, String, ss, k), xs)) : {_ <> G.groups(r, xs, List.drop(&2, String, ss, k)) == Glob.sp_groups(k <> r, xs, ss) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, G.groups(r, xs, List.drop(&2, String, ss, k)), Glob.sp_groups(r, xs, List.drop(&2, String, ss, k)), gq.groups(r, xs, List.drop(&2, String, ss, k))) : {Glob.sp_hit(List.take(&2, String, ss, k), xs) <> _ == Glob.sp_groups(k <> r, xs, ss) : List<&2, Bool>}
      {==}
