# eukhe: lemmas the proofs of area theme share

import Base
import ../../bend/color.bend as Co
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ../base/bool/misc.bend as LBoolMisc

def themes.pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : LBoolMisc.themes.pt.BD(_, A, Unit)
  Unit{}

def themes.pt.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      themes.pt.absurdF({False{} == True{} : Bool}, h)

def themes.pt.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      themes.pt.absurdF({b == True{} : Bool}, h)

def themes.pt.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pt.or_false_l(c: Bool, +d: Bool, h: {Bool.or(c, d) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      {==}

def themes.pt.or_false_r(c: Bool, +d: Bool, h: {Bool.or(c, d) == False{} : Bool}) -> {d == False{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, True{}, False{}, h) : LBoolMisc.themes.pt.BD(_, {d == False{} : Bool}, Unit)
      Unit{}
    case False{}:
      h

def themes.pt.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  themes.pt.absurdF(A, Equal.sym(Bool, True{}, False{}, e))

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
      +here = pt.fill_some(T.kind(t), cols, bg, t, themes.pt.and_l(T.ok(cols, t), T.valid.go(cols, rest), h))
      +more = pt.complete(cols, bg, rest, themes.pt.and_r(T.ok(cols, t), T.valid.go(cols, rest), h))
      themes.pt.and_t(Maybe.is_some(&2, T.Val, T.fill(cols, bg, t)), T.complete(T.fill.map(cols, bg, rest)), here, more)

def theme_tokens_complete(f: T.Th, v: {T.valid(f) == True{} : Bool}) -> {T.complete(T.palette(f)) == True{} : Bool}:
  match f:
    case T.Th{name, +cols, +page, card, info}:
      pt.complete(cols, T.background(cols, page), T.toks(), v)

def pt.cons_all(r: T.EntR, es: List<&2, T.Ent>, hg: {Theme.th.good(r) == True{} : Bool}) -> {T.ents.cons(r, T.All{es}) == T.All{Theme.th.ent(r) <> es} : T.Ents}:
  match r:
    case T.Good{e}:
      {==}
    case T.Bad{x}:
      themes.pt.absurdF({T.ents.cons(T.Bad{x}, T.All{es}) == T.All{Theme.th.ent(T.Bad{x}) <> es} : T.Ents}, hg)

def pt.ents_all(+vars: List<&2, T.Var>, +cols: List<&2, T.REnt>, +ok: {Theme.th.clean(vars, cols) == True{} : Bool}) -> {T.ents(T.index(vars), cols) == T.All{Theme.th.goods(vars, cols)} : T.Ents}:
  match cols:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      +hg = themes.pt.and_l(Theme.th.good(T.entry(vars, x)), Theme.th.clean(vars, rest), ok)
      +ih = pt.ents_all(vars, rest, themes.pt.and_r(Theme.th.good(T.entry(vars, x)), Theme.th.clean(vars, rest), ok))
      %Equal.sym(T.Ents, T.ents(T.index(vars), rest), T.All{Theme.th.goods(vars, rest)}, ih) : {T.ents.cons(T.entry(vars, x), _) == T.All{Theme.th.ent(T.entry(vars, x)) <> Theme.th.goods(vars, rest)} : T.Ents}
      pt.cons_all(T.entry(vars, x), Theme.th.goods(vars, rest), hg)

def pt.keeps(c: Bool, +t: U32, -m: List<&2, U32>, -a: List<&2, U32>, ih: {m == a : List<&2, U32>}) -> {T.missing.keep(c, t, m) == Theme.th.keep(c, t, a) : List<&2, U32>}:
  match c:
    case True{}:
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => t <> xs, m, a, ih)
    case False{}:
      ih

def pt.miss_case(r: Bool, +es: List<&2, T.Ent>, +t: U32, +rest: List<&2, U32>, ih: {T.missing.go(es, rest) == Theme.th.absent.go(es, Theme.th.reqs(rest)) : List<&2, U32>})
  -> {T.missing.keep(Bool.and(r, Bool.not(T.has(es, t))), t, T.missing.go(es, rest)) == Theme.th.absent.go(es, Theme.th.keep(r, t, Theme.th.reqs(rest))) : List<&2, U32>}:
  match r:
    case True{}:
      pt.keeps(Bool.not(T.has(es, t)), t, T.missing.go(es, rest), Theme.th.absent.go(es, Theme.th.reqs(rest)), ih)
    case False{}:
      ih

def pt.miss_step(+r: Bool, +es: List<&2, T.Ent>, +t: U32, +rest: List<&2, U32>, er: {T.required(t) == r : Bool}, ih: {T.missing.go(es, rest) == Theme.th.absent.go(es, Theme.th.reqs(rest)) : List<&2, U32>})
  -> {T.missing.go(es, t <> rest) == Theme.th.absent.go(es, Theme.th.reqs(t <> rest)) : List<&2, U32>}:
  %Equal.sym(Bool, T.required(t), r, er) : {T.missing.keep(Bool.and(_, Bool.not(T.has(es, t))), t, T.missing.go(es, rest)) == Theme.th.absent.go(es, Theme.th.keep(_, t, Theme.th.reqs(rest))) : List<&2, U32>}
  pt.miss_case(r, es, t, rest, ih)

def pt.miss_go(+es: List<&2, T.Ent>, +ts: List<&2, U32>) -> {T.missing.go(es, ts) == Theme.th.absent.go(es, Theme.th.reqs(ts)) : List<&2, U32>}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      pt.miss_step(T.required(t), es, t, rest, {==}, pt.miss_go(es, rest))

def pt.missing_absent(+es: List<&2, T.Ent>) -> {T.missing(es) == Theme.th.absent(es) : List<&2, U32>}:
  pt.miss_go(es, T.toks())

# a file whose entries read and whose required tokens are written reads
# to its export backgrounds
def pt.read_end(+nm: String, +vars: List<&2, T.Var>, +cols: List<&2, T.REnt>, +pg: Maybe<&2, T.Json>, +cd: Maybe<&2, T.Json>, +io: Maybe<&2, T.Json>, +ok: {Theme.th.clean(vars, cols) == True{} : Bool}, +all: {Theme.th.absent(Theme.th.goods(vars, cols)) == [] : List<&2, U32>})
  -> {T.read(T.RFile{nm, vars, cols, pg, cd, io}) == T.read.end(nm, Theme.th.goods(vars, cols), T.surf(T.index(vars), T.OnPage{}, pg), T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, io)) : T.Read}:
  +gs = Theme.th.goods(vars, cols)
  +rhs = T.read.end(nm, gs, T.surf(T.index(vars), T.OnPage{}, pg), T.surf(T.index(vars), T.OnCard{}, cd), T.surf(T.index(vars), T.OnInfo{}, io))
  +mn = Equal.trans(List<&2, U32>, T.missing(gs), Theme.th.absent(gs), Nil{}, pt.missing_absent(gs), all)
  %Equal.sym(T.Ents, T.ents(T.index(vars), cols), T.All{gs}, pt.ents_all(vars, cols, ok)) : {T.read.cols(nm, T.index(vars), _, pg, cd, io) == rhs : T.Read}
  %Equal.sym(List<&2, U32>, T.missing(gs), Nil{}, mn) : {T.read.full(nm, T.index(vars), gs, _, pg, cd, io) == rhs : T.Read}
  {==}

def pt.surf_hit(at: T.Surf, g: T.Got, h: {Theme.th.hit(g) == True{} : Bool}) -> {T.surf.got(at, g) == T.BgOk{Theme.th.hitc(g)} : T.Bg}:
  match g:
    case T.Hit{v}:
      {==}
    case T.Miss{why}:
      themes.pt.absurdF({T.surf.got(at, T.Miss{why}) == T.BgOk{Theme.th.hitc(T.Miss{why})} : T.Bg}, h)

def pt.surf_fine(+vars: List<&2, T.Var>, at: T.Surf, m: Maybe<&2, T.Json>, h: {Theme.th.fine(vars, m) == True{} : Bool}) -> {T.surf(T.index(vars), at, m) == T.BgOk{Theme.th.bgv(vars, m)} : T.Bg}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      pt.surf_hit(at, T.chase(vars, j), h)

# Picking a theme
# ---------------
# The model's candidates, cause, broken list and clashes are the rule's,
# step by step; the theme picked is the resolution over the candidates.

def pt.cand(l: T.Ld, +c: Bool, +at: Nat, rest: List<&2, T.Cand>) -> {T.cands.of(l, c, at, rest) == List.append(&2, T.Cand, Theme.th.cand(l, c, at), rest) : List<&2, T.Cand>}:
  match l:
    case T.Fine{nm, k}:
      match k:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case T.Broke{nm, st}:
      {==}

def pt.cands(ls: List<&2, T.Ld>, +c: Bool, +at: Nat) -> {T.cands(ls, c, at) == Theme.th.cands(ls, c, at) : List<&2, T.Cand>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(List<&2, T.Cand>, T.cands(rest, c, 1n+at), Theme.th.cands(rest, c, 1n+at), pt.cands(rest, c, 1n+at)) : {T.cands.of(l, c, at, _) == List.append(&2, T.Cand, Theme.th.cand(l, c, at), Theme.th.cands(rest, c, 1n+at)) : List<&2, T.Cand>}
      pt.cand(l, c, at, Theme.th.cands(rest, c, 1n+at))

def pt.pickres(+ls: List<&2, T.Ld>, +n: String) -> {T.pick.res(ls, n) == Theme.th.pick(ls, n) : T.Res}:
  %Equal.sym(List<&2, T.Cand>, T.cands(ls, False{}, 0n), Theme.th.cands(ls, False{}, 0n), pt.cands(ls, False{}, 0n)) : {T.resolve.name(T.sources(_, T.cands(ls, True{}, 0n)), n) == Theme.th.pick(ls, n) : T.Res}
  %Equal.sym(List<&2, T.Cand>, T.cands(ls, True{}, 0n), Theme.th.cands(ls, True{}, 0n), pt.cands(ls, True{}, 0n)) : {T.resolve.name(T.sources(Theme.th.cands(ls, False{}, 0n), _), n) == Theme.th.pick(ls, n) : T.Res}
  {==}

def pt.blames(l: T.Ld, +n: String) -> {T.blames(l, n) == Theme.th.blames(l, n) : Bool}:
  match l:
    case T.Fine{nm, c}:
      {==}
    case T.Broke{nm, st}:
      match nm:
        case Some{x}:
          {==}
        case None{}:
          match st:
            case Some{s}:
              {==}
            case None{}:
              {==}

def pt.first_if(hit: Bool, at: Nat, -a: Maybe<&2, Nat>, -b: Maybe<&2, Nat>, e: {a == b : Maybe<&2, Nat>}) -> {T.first.pick(hit, at, a) == Theme.th.at.if(hit, at, b) : Maybe<&2, Nat>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      e

def pt.cause_go(ls: List<&2, T.Ld>, +n: String, +at: Nat) -> {T.cause.go(ls, n, at) == Theme.th.blame(ls, n, at) : Maybe<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(Bool, T.blames(l, n), Theme.th.blames(l, n), pt.blames(l, n)) : {T.first.pick(_, at, T.cause.go(rest, n, 1n+at)) == Theme.th.at.if(Theme.th.blames(l, n), at, Theme.th.blame(rest, n, 1n+at)) : Maybe<&2, Nat>}
      pt.first_if(Theme.th.blames(l, n), at, T.cause.go(rest, n, 1n+at), Theme.th.blame(rest, n, 1n+at), pt.cause_go(rest, n, 1n+at))

def pt.pick_w(+ls: List<&2, T.Ld>, +n: String, +id: U32, +w: Bool, +h: {Theme.th.pick(ls, n) == T.Res{id, w} : T.Res}) -> {T.pick(ls, n) == T.pick.warn(w, id, ls, n) : T.Pick}:
  +e = Equal.trans(T.Res, T.pick.res(ls, n), Theme.th.pick(ls, n), T.Res{id, w}, pt.pickres(ls, n), h)
  %Equal.sym(T.Res, T.pick.res(ls, n), T.Res{id, w}, e) : {T.pick.go(_, ls, n) == T.pick.warn(w, id, ls, n) : T.Pick}
  {==}
