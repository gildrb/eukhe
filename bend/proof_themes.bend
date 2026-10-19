# proof_themes: the T1 laws (docs/interface.md Themes) of the theme model
# in bend/theme.bend.
#
# Resolution scans the candidates in order: a candidate that does not
# resolve the name passes the scan on, so before the first one that does
# the scan finds nothing, and with none at all it ends at the default
# theme with a warning. A loaded file passed the validity check. The
# validity check asks of each token what its fill needs, so the fill of
# every token of a valid file has a value. The mode and the palette read
# only the colors and the export page, never the name. The shipped
# themes' contrasts and 256-color indices are finite: the checker
# computes them.

import Base
import ./theme.bend as T
import ./color.bend as Co

# Logic
# -----

def pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pt.BD(_, A, Unit)
  Unit{}

def pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pt.absurdF({False{} == True{} : Bool}, h)

def pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pt.absurdF({b == True{} : Bool}, h)

def pt.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pt.or_false_l(c: Bool, +d: Bool, h: {Bool.or(c, d) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      {==}

def pt.or_false_r(c: Bool, +d: Bool, h: {Bool.or(c, d) == False{} : Bool}) -> {d == False{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, True{}, False{}, h) : pt.BD(_, {d == False{} : Bool}, Unit)
      Unit{}
    case False{}:
      h

# Resolution
# ----------

# a scan of candidates none of which resolves n ends at the default theme,
# with a warning
def pt.find_miss(+src: List<&2, T.Cand>, +n: String, +miss: {T.hit(src, n) == False{} : Bool}) -> {T.find(src, n) == T.Res{T.dflt(), True{}} : T.Res}:
  match src:
    case Nil{}:
      {==}
    case Con{T.Cand{nm, v, id}, rest}:
      +here = pt.or_false_l(T.names(T.Cand{nm, v, id}, n), T.hit(rest, n), miss)
      %Equal.sym(Bool, T.names(T.Cand{nm, v, id}, n), False{}, here) : {T.find.pick(_, id, T.find(rest, n)) == T.Res{T.dflt(), True{}} : T.Res}
      pt.find_miss(rest, n, pt.or_false_r(T.names(T.Cand{nm, v, id}, n), T.hit(rest, n), miss))

# a scan whose candidates before c do not resolve n finds c
def pt.find_first(+pre: List<&2, T.Cand>, +nm: String, +id: U32, +post: List<&2, T.Cand>, +n: String, +miss: {T.hit(pre, n) == False{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {T.find(List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, String.eq(nm, n), True{}, same) : {T.find.pick(Bool.and(True{}, _), id, T.find(post, n)) == T.Res{id, False{}} : T.Res}
      {==}
    case Con{T.Cand{pn, pv, pid}, rest}:
      +here = pt.or_false_l(T.names(T.Cand{pn, pv, pid}, n), T.hit(rest, n), miss)
      %Equal.sym(Bool, T.names(T.Cand{pn, pv, pid}, n), False{}, here) : {T.find.pick(_, pid, T.find(List.append(&2, T.Cand, rest, T.Cand{nm, True{}, id} <> post), n)) == T.Res{id, False{}} : T.Res}
      pt.find_first(rest, nm, id, post, n, pt.or_false_r(T.names(T.Cand{pn, pv, pid}, n), T.hit(rest, n), miss), same)

def theme_resolve_empty(src: List<&2, T.Cand>) -> {T.resolve.name(src, "") == T.Res{T.dflt(), False{}} : T.Res}:
  {==}

def theme_resolve_first(+pre: List<&2, T.Cand>, +nm: String, +id: U32, +post: List<&2, T.Cand>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, miss: {T.hit(pre, n) == False{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {T.resolve.name(List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}:
  %Equal.sym(Bool, String.is_empty(n), False{}, ne) : {T.resolve.name.pick(_, List.append(&2, T.Cand, pre, T.Cand{nm, True{}, id} <> post), n) == T.Res{id, False{}} : T.Res}
  pt.find_first(pre, nm, id, post, n, miss, same)

def theme_resolve_missing(+src: List<&2, T.Cand>, +n: String, ne: {String.is_empty(n) == False{} : Bool}, miss: {T.hit(src, n) == False{} : Bool})
  -> {T.resolve.name(src, n) == T.Res{T.dflt(), True{}} : T.Res}:
  %Equal.sym(Bool, String.is_empty(n), False{}, ne) : {T.resolve.name.pick(_, src, n) == T.Res{T.dflt(), True{}} : T.Res}
  pt.find_miss(src, n, miss)

# Loading and completion
# ----------------------

def pt.some_inj(-A: Data, -a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => T.or_else(A, m, a), Some{a}, Some{b}, e)

def pt.none_some(-A: Type, -B: Data, -b: B, e: {None{} == Some{b} : Maybe<&2, B>}) -> A:
  %e : pt.BD(Maybe.is_some(&2, B, _), A, Unit)
  Unit{}

def pt.keep(ok: Bool, +g: T.Th, -f: T.Th, eo: {T.valid(g) == ok : Bool}, h: {T.load.keep(ok, g) == Some{f} : Maybe<&2, T.Th>}) -> {T.valid(f) == True{} : Bool}:
  match ok:
    case True{}:
      %pt.some_inj(T.Th, g, f, h) : {T.valid(_) == True{} : Bool}
      eo
    case False{}:
      pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)

def pt.check(+name: String, +cs: Maybe<&2, List<&2, T.Ent>>, +pg: Maybe<&2, Maybe<&2, Co.Rgb>>, -f: T.Th, h: {T.load.check(name, cs, pg) == Some{f} : Maybe<&2, T.Th>}) -> {T.valid(f) == True{} : Bool}:
  match cs pg:
    case Some{c} Some{p}:
      pt.keep(T.valid(T.Th{name, c, p}), T.Th{name, c, p}, f, {==}, h)
    case Some{c} None{}:
      pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)
    case None{} Some{p}:
      pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)
    case None{} None{}:
      pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)

def theme_load_valid(r: T.RFile, -f: T.Th, loaded: {T.load(r) == Some{f} : Maybe<&2, T.Th>}) -> {T.valid(f) == True{} : Bool}:
  match r:
    case T.RFile{name, +vars, cols, page}:
      pt.check(name, T.resolve.cols(vars, cols), T.load.page(vars, page), f, loaded)

def pt.or_some(a: Maybe<&2, T.Val>, +b: Maybe<&2, T.Val>, h: {Bool.or(Maybe.is_some(&2, T.Val, a), Maybe.is_some(&2, T.Val, b)) == True{} : Bool})
  -> {Maybe.is_some(&2, T.Val, T.or(T.Val, a, b)) == True{} : Bool}:
  match a:
    case None{}:
      h
    case Some{x}:
      {==}

def pt.fill_some(k: T.Role, +cols: List<&2, T.Ent>, +bg: Co.Rgb, +t: U32, h: {T.ok.k(k, cols, t) == True{} : Bool})
  -> {Maybe.is_some(&2, T.Val, T.fill.k(k, cols, bg, t)) == True{} : Bool}:
  match k:
    case T.Req{}:
      h
    case T.MdBody{}:
      pt.or_some(T.get(cols, t), T.get(cols, 9), h)
    case T.RefHeader{}:
      {==}
    case T.RefSummary{}:
      {==}
    case T.Background{}:
      {==}
    case T.Foreground{}:
      {==}

def pt.complete(+cols: List<&2, T.Ent>, +bg: Co.Rgb, +ts: List<&2, U32>, +h: {T.valid.go(cols, ts) == True{} : Bool})
  -> {T.complete(T.fill.map(cols, bg, ts)) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      +here = pt.fill_some(T.kind(t), cols, bg, t, pt.and_l(T.ok(cols, t), T.valid.go(cols, rest), h))
      +more = pt.complete(cols, bg, rest, pt.and_r(T.ok(cols, t), T.valid.go(cols, rest), h))
      pt.and_t(Maybe.is_some(&2, T.Val, T.fill(cols, bg, t)), T.complete(T.fill.map(cols, bg, rest)), here, more)

def theme_tokens_complete(f: T.Th, v: {T.valid(f) == True{} : Bool}) -> {T.complete(T.palette(f)) == True{} : Bool}:
  match f:
    case T.Th{name, +cols, +page}:
      pt.complete(cols, T.background(cols, page), T.toks(), v)

# Modes and names
# ---------------

def pt.light_bg(f: T.Th) -> {T.light(f) == Co.light(T.bg(f)) : Bool}:
  match f:
    case T.Th{name, cols, page}:
      {==}

def theme_mode_background(f: T.Th, g: T.Th, same: {T.bg(f) == T.bg(g) : Co.Rgb}) -> {T.light(f) == T.light(g) : Bool}:
  +lf = pt.light_bg(f)
  +lg = pt.light_bg(g)
  %Equal.sym(Bool, T.light(f), Co.light(T.bg(f)), lf) : {_ == T.light(g) : Bool}
  %Equal.sym(Bool, T.light(g), Co.light(T.bg(g)), lg) : {Co.light(T.bg(f)) == _ : Bool}
  Equal.cong(Co.Rgb, Bool, c => Co.light(c), T.bg(f), T.bg(g), same)

def theme_palette_name_free(f: T.Th, n: String) -> {T.palette(T.rename(f, n)) == T.palette(f) : List<&2, Maybe<&2, T.Val>>}:
  match f:
    case T.Th{name, cols, page}:
      {==}

def theme_mode_name_free(f: T.Th, n: String) -> {T.light(T.rename(f, n)) == T.light(f) : Bool}:
  match f:
    case T.Th{name, cols, page}:
      {==}

# Shipped themes
# --------------

def theme_shipped_legible(s: T.Shipped) -> {T.legible(T.table(s)) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}

def theme_shipped_status_distinct(s: T.Shipped) -> {T.status_distinct(T.table(s)) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}
