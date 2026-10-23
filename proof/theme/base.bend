# eukhe: lemmas the proofs of area theme share

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/name.bend as TName
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/token.bend as TToken
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

def pt.or_some(a: Maybe<&2, TFile.Val>, +b: Maybe<&2, TFile.Val>, h: {Bool.or(Maybe.is_some(&2, TFile.Val, a), Maybe.is_some(&2, TFile.Val, b)) == True{} : Bool})
  -> {Maybe.is_some(&2, TFile.Val, TPalette.or(TFile.Val, a, b)) == True{} : Bool}:
  match a:
    case None{}:
      h
    case Some{x}:
      {==}

def pt.fill_some(k: TToken.Role, +cols: List<&2, TFile.Ent>, +bg: Co.Rgb, +t: U32, h: {TToken.ok.k(k, cols, t) == True{} : Bool})
  -> {Maybe.is_some(&2, TFile.Val, TPalette.fill.k(k, cols, bg, t)) == True{} : Bool}:
  match k:
    case TToken.Req{}:
      h
    case TToken.MdBody{}:
      pt.or_some(TToken.get(cols, t), TToken.get(cols, 9), h)
    case TToken.RefHeader{}:
      {==}
    case TToken.RefSummary{}:
      {==}
    case TToken.Background{}:
      {==}
    case TToken.Foreground{}:
      {==}

def pt.complete(+cols: List<&2, TFile.Ent>, +bg: Co.Rgb, +ts: List<&2, U32>, +h: {TToken.valid.go(cols, ts) == True{} : Bool})
  -> {TPalette.complete(TPalette.fill.map(cols, bg, ts)) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      +here = pt.fill_some(TToken.kind(t), cols, bg, t, themes.pt.and_l(TToken.ok(cols, t), TToken.valid.go(cols, rest), h))
      +more = pt.complete(cols, bg, rest, themes.pt.and_r(TToken.ok(cols, t), TToken.valid.go(cols, rest), h))
      themes.pt.and_t(Maybe.is_some(&2, TFile.Val, TPalette.fill(cols, bg, t)), TPalette.complete(TPalette.fill.map(cols, bg, rest)), here, more)

def theme_tokens_complete(f: TFile.Th, v: {TToken.valid(f) == True{} : Bool}) -> {TPalette.complete(TPalette.palette(f)) == True{} : Bool}:
  match f:
    case TFile.Th{name, +cols, +page, card, info}:
      pt.complete(cols, TPalette.background(cols, page), TToken.toks(), v)

def pt.cons_all(r: TReader.EntR, es: List<&2, TFile.Ent>, hg: {Theme.th.good(r) == True{} : Bool}) -> {TReader.ents.cons(r, TReader.All{es}) == TReader.All{Theme.th.ent(r) <> es} : TReader.Ents}:
  match r:
    case TReader.Good{e}:
      {==}
    case TReader.Bad{x}:
      themes.pt.absurdF({TReader.ents.cons(TReader.Bad{x}, TReader.All{es}) == TReader.All{Theme.th.ent(TReader.Bad{x}) <> es} : TReader.Ents}, hg)

def pt.ents_all(+vars: List<&2, TFile.Var>, +cols: List<&2, TFile.REnt>, +ok: {Theme.th.clean(vars, cols) == True{} : Bool}) -> {TReader.ents(TChase.index(vars), cols) == TReader.All{Theme.th.goods(vars, cols)} : TReader.Ents}:
  match cols:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      +hg = themes.pt.and_l(Theme.th.good(TReader.entry(vars, x)), Theme.th.clean(vars, rest), ok)
      +ih = pt.ents_all(vars, rest, themes.pt.and_r(Theme.th.good(TReader.entry(vars, x)), Theme.th.clean(vars, rest), ok))
      %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), rest), TReader.All{Theme.th.goods(vars, rest)}, ih) : {TReader.ents.cons(TReader.entry(vars, x), _) == TReader.All{Theme.th.ent(TReader.entry(vars, x)) <> Theme.th.goods(vars, rest)} : TReader.Ents}
      pt.cons_all(TReader.entry(vars, x), Theme.th.goods(vars, rest), hg)

def pt.keeps(c: Bool, +t: U32, -m: List<&2, U32>, -a: List<&2, U32>, ih: {m == a : List<&2, U32>}) -> {TReader.missing.keep(c, t, m) == Theme.th.keep(c, t, a) : List<&2, U32>}:
  match c:
    case True{}:
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => t <> xs, m, a, ih)
    case False{}:
      ih

def pt.miss_case(r: Bool, +es: List<&2, TFile.Ent>, +t: U32, +rest: List<&2, U32>, ih: {TReader.missing.go(es, rest) == Theme.th.absent.go(es, Theme.th.reqs(rest)) : List<&2, U32>})
  -> {TReader.missing.keep(Bool.and(r, Bool.not(TToken.has(es, t))), t, TReader.missing.go(es, rest)) == Theme.th.absent.go(es, Theme.th.keep(r, t, Theme.th.reqs(rest))) : List<&2, U32>}:
  match r:
    case True{}:
      pt.keeps(Bool.not(TToken.has(es, t)), t, TReader.missing.go(es, rest), Theme.th.absent.go(es, Theme.th.reqs(rest)), ih)
    case False{}:
      ih

def pt.miss_step(+r: Bool, +es: List<&2, TFile.Ent>, +t: U32, +rest: List<&2, U32>, er: {TReader.required(t) == r : Bool}, ih: {TReader.missing.go(es, rest) == Theme.th.absent.go(es, Theme.th.reqs(rest)) : List<&2, U32>})
  -> {TReader.missing.go(es, t <> rest) == Theme.th.absent.go(es, Theme.th.reqs(t <> rest)) : List<&2, U32>}:
  %Equal.sym(Bool, TReader.required(t), r, er) : {TReader.missing.keep(Bool.and(_, Bool.not(TToken.has(es, t))), t, TReader.missing.go(es, rest)) == Theme.th.absent.go(es, Theme.th.keep(_, t, Theme.th.reqs(rest))) : List<&2, U32>}
  pt.miss_case(r, es, t, rest, ih)

def pt.miss_go(+es: List<&2, TFile.Ent>, +ts: List<&2, U32>) -> {TReader.missing.go(es, ts) == Theme.th.absent.go(es, Theme.th.reqs(ts)) : List<&2, U32>}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      pt.miss_step(TReader.required(t), es, t, rest, {==}, pt.miss_go(es, rest))

def pt.missing_absent(+es: List<&2, TFile.Ent>) -> {TReader.missing(es) == Theme.th.absent(es) : List<&2, U32>}:
  pt.miss_go(es, TToken.toks())

# a file whose entries read and whose required tokens are written reads
# to its export backgrounds
def pt.read_end(+nm: String, +vars: List<&2, TFile.Var>, +cols: List<&2, TFile.REnt>, +pg: Maybe<&2, TFile.Json>, +cd: Maybe<&2, TFile.Json>, +io: Maybe<&2, TFile.Json>, +ok: {Theme.th.clean(vars, cols) == True{} : Bool}, +all: {Theme.th.absent(Theme.th.goods(vars, cols)) == [] : List<&2, U32>})
  -> {TReader.read(TFile.RFile{nm, vars, cols, pg, cd, io}) == TReader.read.end(nm, Theme.th.goods(vars, cols), TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)) : TReader.Read}:
  +gs = Theme.th.goods(vars, cols)
  +rhs = TReader.read.end(nm, gs, TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io))
  +mn = Equal.trans(List<&2, U32>, TReader.missing(gs), Theme.th.absent(gs), Nil{}, pt.missing_absent(gs), all)
  %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), cols), TReader.All{gs}, pt.ents_all(vars, cols, ok)) : {TReader.read.cols(nm, TChase.index(vars), _, pg, cd, io) == rhs : TReader.Read}
  %Equal.sym(List<&2, U32>, TReader.missing(gs), Nil{}, mn) : {TReader.read.full(nm, TChase.index(vars), gs, _, pg, cd, io) == rhs : TReader.Read}
  {==}

def pt.surf_hit(at: TFile.Surf, g: TChase.Got, h: {Theme.th.hit(g) == True{} : Bool}) -> {TReader.surf.got(at, g) == TReader.BgOk{Theme.th.hitc(g)} : TReader.Bg}:
  match g:
    case TChase.Hit{v}:
      {==}
    case TChase.Miss{why}:
      themes.pt.absurdF({TReader.surf.got(at, TChase.Miss{why}) == TReader.BgOk{Theme.th.hitc(TChase.Miss{why})} : TReader.Bg}, h)

def pt.surf_fine(+vars: List<&2, TFile.Var>, at: TFile.Surf, m: Maybe<&2, TFile.Json>, h: {Theme.th.fine(vars, m) == True{} : Bool}) -> {TReader.surf(TChase.index(vars), at, m) == TReader.BgOk{Theme.th.bgv(vars, m)} : TReader.Bg}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      pt.surf_hit(at, TChase.chase(vars, j), h)

# Picking a theme
# ---------------
# The model's candidates, cause, broken list and clashes are the rule's,
# step by step; the theme picked is the resolution over the candidates.

def pt.cand(l: TChoice.Ld, +c: Bool, +at: Nat, rest: List<&2, TName.Cand>) -> {TChoice.cands.of(l, c, at, rest) == List.append(&2, TName.Cand, Theme.th.cand(l, c, at), rest) : List<&2, TName.Cand>}:
  match l:
    case TChoice.Fine{nm, k}:
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
    case TChoice.Broke{nm, st}:
      {==}

def pt.cands(ls: List<&2, TChoice.Ld>, +c: Bool, +at: Nat) -> {TChoice.cands(ls, c, at) == Theme.th.cands(ls, c, at) : List<&2, TName.Cand>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(List<&2, TName.Cand>, TChoice.cands(rest, c, 1n+at), Theme.th.cands(rest, c, 1n+at), pt.cands(rest, c, 1n+at)) : {TChoice.cands.of(l, c, at, _) == List.append(&2, TName.Cand, Theme.th.cand(l, c, at), Theme.th.cands(rest, c, 1n+at)) : List<&2, TName.Cand>}
      pt.cand(l, c, at, Theme.th.cands(rest, c, 1n+at))

def pt.pickres(+ls: List<&2, TChoice.Ld>, +n: String) -> {TChoice.pick.res(ls, n) == Theme.th.pick(ls, n) : TName.Res}:
  %Equal.sym(List<&2, TName.Cand>, TChoice.cands(ls, False{}, 0n), Theme.th.cands(ls, False{}, 0n), pt.cands(ls, False{}, 0n)) : {TName.resolve.name(TName.sources(_, TChoice.cands(ls, True{}, 0n)), n) == Theme.th.pick(ls, n) : TName.Res}
  %Equal.sym(List<&2, TName.Cand>, TChoice.cands(ls, True{}, 0n), Theme.th.cands(ls, True{}, 0n), pt.cands(ls, True{}, 0n)) : {TName.resolve.name(TName.sources(Theme.th.cands(ls, False{}, 0n), _), n) == Theme.th.pick(ls, n) : TName.Res}
  {==}

def pt.blames(l: TChoice.Ld, +n: String) -> {TChoice.blames(l, n) == Theme.th.blames(l, n) : Bool}:
  match l:
    case TChoice.Fine{nm, c}:
      {==}
    case TChoice.Broke{nm, st}:
      match nm:
        case Some{x}:
          {==}
        case None{}:
          match st:
            case Some{s}:
              {==}
            case None{}:
              {==}

def pt.first_if(hit: Bool, at: Nat, -a: Maybe<&2, Nat>, -b: Maybe<&2, Nat>, e: {a == b : Maybe<&2, Nat>}) -> {TChoice.first.pick(hit, at, a) == Theme.th.at.if(hit, at, b) : Maybe<&2, Nat>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      e

def pt.cause_go(ls: List<&2, TChoice.Ld>, +n: String, +at: Nat) -> {TChoice.cause.go(ls, n, at) == Theme.th.blame(ls, n, at) : Maybe<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(Bool, TChoice.blames(l, n), Theme.th.blames(l, n), pt.blames(l, n)) : {TChoice.first.pick(_, at, TChoice.cause.go(rest, n, 1n+at)) == Theme.th.at.if(Theme.th.blames(l, n), at, Theme.th.blame(rest, n, 1n+at)) : Maybe<&2, Nat>}
      pt.first_if(Theme.th.blames(l, n), at, TChoice.cause.go(rest, n, 1n+at), Theme.th.blame(rest, n, 1n+at), pt.cause_go(rest, n, 1n+at))

def pt.pick_w(+ls: List<&2, TChoice.Ld>, +n: String, +id: U32, +w: Bool, +h: {Theme.th.pick(ls, n) == TName.Res{id, w} : TName.Res}) -> {TChoice.pick(ls, n) == TChoice.pick.warn(w, id, ls, n) : TChoice.Pick}:
  +e = Equal.trans(TName.Res, TChoice.pick.res(ls, n), Theme.th.pick(ls, n), TName.Res{id, w}, pt.pickres(ls, n), h)
  %Equal.sym(TName.Res, TChoice.pick.res(ls, n), TName.Res{id, w}, e) : {TChoice.pick.go(_, ls, n) == TChoice.pick.warn(w, id, ls, n) : TChoice.Pick}
  {==}
