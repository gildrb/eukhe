# eukhe: lemmas of the proof of glob_allowed: trimming, the wildcard
# test, the bare id and each pattern's verdict are the spec's.

import Base
import ../../../bend/glob.bend as G
import ../../../laws/glob.bend as Glob
import ./items.bend as GI
import ./query.bend as GQ

def ga.ws(c: Char) -> {G.ws(c) == Glob.sp_ws(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def ga.drop.k(b: Bool, c: Char, t: String, rest: String) -> {G.trim_start.k(b, c, t, rest) == Glob.sp_drop_ws.k(b, c, t, rest) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ga.drop(s: String) -> {G.trim_start(s) == Glob.sp_drop_ws(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, G.ws(c), Glob.sp_ws(c), ga.ws(c)) : {G.trim_start.k(_, c, t, G.trim_start(t)) == Glob.sp_drop_ws(SCon{c, t}) : String}
      %Equal.sym(String, G.trim_start(t), Glob.sp_drop_ws(t), ga.drop(t)) : {G.trim_start.k(Glob.sp_ws(c), c, t, _) == Glob.sp_drop_ws(SCon{c, t}) : String}
      ga.drop.k(Glob.sp_ws(c), c, t, Glob.sp_drop_ws(t))

def ga.trim(+s: String) -> {G.trim(s) == Glob.sp_trim(s) : String}:
  %Equal.sym(String, G.trim_start(s), Glob.sp_drop_ws(s), ga.drop(s)) : {String.reverse(G.trim_start(String.reverse(_))) == Glob.sp_trim(s) : String}
  %Equal.sym(String, G.trim_start(String.reverse(Glob.sp_drop_ws(s))), Glob.sp_drop_ws(String.reverse(Glob.sp_drop_ws(s))), ga.drop(String.reverse(Glob.sp_drop_ws(s)))) : {String.reverse(_) == Glob.sp_trim(s) : String}
  {==}

def ga.wild(s: String) -> {G.wild(s) == Glob.sp_wild(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          %Equal.sym(Bool, G.wild(t), Glob.sp_wild(t), ga.wild(t)) : {Bool.or(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), U32.is_eq(x, 91))), _) == Glob.sp_wild(SCon{Chr{x}, t}) : Bool}
          {==}

def ga.bare.k(b: Bool, +t: String, +orig: String, ih: {G.bare.k(orig, G.after_slash(t)) == Glob.sp_bare.go(t, orig) : String}) -> {G.bare.k(orig, G.after_slash.k(b, t, G.after_slash(t))) == Glob.sp_bare.k(b, t, Glob.sp_bare.go(t, orig)) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def ga.bare.go(s: String, +orig: String) -> {G.bare.k(orig, G.after_slash(s)) == Glob.sp_bare.go(s, orig) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          ga.bare.k(U32.is_eq(x, 47), t, orig, ga.bare.go(t, orig))

def ga.bare(+s: String) -> {G.bare(s) == Glob.sp_bare(s) : String}:
  ga.bare.go(s, s)

def ga.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ga.g(r: Result<&2, &2, G.Err, G.Glob>, +sel: String) -> {G.allow.g(r, sel) == Glob.sp_allow.g(r, sel) : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+g}:
      +o = {G.Opts{False{}, False{}} : G.Opts}
      %Equal.sym(Bool, G.hit_any([sel, G.bare(sel)], G.items(o, g)), Glob.sp_hit([sel, G.bare(sel)], G.items(o, g)), GQ.gq.hit([sel, G.bare(sel)], G.items(o, g))) : {_ == Glob.sp_allow.g(Done{g}, sel) : Bool}
      %Equal.sym(List<&2, List<&2, G.It>>, G.items(o, g), Glob.sp_items(o, g), GI.gi.items(o, g)) : {Glob.sp_hit([sel, G.bare(sel)], _) == Glob.sp_allow.g(Done{g}, sel) : Bool}
      %Equal.sym(String, G.bare(sel), Glob.sp_bare(sel), ga.bare(sel)) : {Glob.sp_hit([sel, _], Glob.sp_items(o, g)) == Glob.sp_allow.g(Done{g}, sel) : Bool}
      %Equal.sym(Bool, Bool.or(Glob.sp_any(G.bytes(Glob.sp_bare(sel)), Glob.sp_items(o, g)), False{}), Glob.sp_any(G.bytes(Glob.sp_bare(sel)), Glob.sp_items(o, g)), ga.or_false(Glob.sp_any(G.bytes(Glob.sp_bare(sel)), Glob.sp_items(o, g)))) : {Bool.or(Glob.sp_any(G.bytes(sel), Glob.sp_items(o, g)), _) == Glob.sp_allow.g(Done{g}, sel) : Bool}
      {==}

def ga.w(w: Bool, +sel: String, +p: String) -> {G.allow.w(w, sel, p) == Glob.sp_allow.w(w, sel, p) : Bool}:
  match w:
    case True{}:
      ga.g(G.parse(p), sel)
    case False{}:
      %Equal.sym(String, G.bare(sel), Glob.sp_bare(sel), ga.bare(sel)) : {Bool.or(String.eq(p, sel), String.eq(p, _)) == Glob.sp_allow.w(False{}, sel, p) : Bool}
      {==}

def ga.e(e: Bool, +sel: String, +p: String) -> {G.allow.e(e, sel, p) == Glob.sp_allow.e(e, sel, p) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, G.wild(p), Glob.sp_wild(p), ga.wild(p)) : {G.allow.w(_, sel, p) == Glob.sp_allow.e(False{}, sel, p) : Bool}
      ga.w(Glob.sp_wild(p), sel, p)

# one pattern's verdict is the spec's
def ga.one(+sel: String, +p: String) -> {G.allow1(sel, p) == Glob.sp_allow1(sel, p) : Bool}:
  %Equal.sym(String, G.trim(p), Glob.sp_trim(p), ga.trim(p)) : {G.allow.e(String.is_empty(_), sel, _) == Glob.sp_allow1(sel, p) : Bool}
  ga.e(String.is_empty(Glob.sp_trim(p)), sel, Glob.sp_trim(p))

def ga.or(b: Bool, +sel: String, r: List<&2, String>, ih: {G.allowed(sel, r) == Glob.sp_allowed(sel, r) : Bool}) -> {G.or_else(b, u => G.allowed(sel, r)) == Bool.or(b, Glob.sp_allowed(sel, r)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the allowlist's verdict is the spec's
def ga.allowed(+sel: String, ps: List<&2, String>) -> {G.allowed(sel, ps) == Glob.sp_allowed(sel, ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +r:
      %Equal.sym(Bool, G.allow1(sel, p), Glob.sp_allow1(sel, p), ga.one(sel, p)) : {G.or_else(_, u => G.allowed(sel, r)) == Glob.sp_allowed(sel, p <> r) : Bool}
      ga.or(Glob.sp_allow1(sel, p), sel, r, ga.allowed(sel, r))
