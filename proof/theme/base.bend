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
import ../base/logic/logic.bend as LLogicLogic

def themes.pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : LLogicLogic.themes.pt.BD(_, A, Unit)
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
      %Equal.sym(Bool, True{}, False{}, h) : LLogicLogic.themes.pt.BD(_, {d == False{} : Bool}, Unit)
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

# Reading a file
# --------------
# The reader's entry is the laws' fault and color of an entry: a key
# that names no token is unknown, a value the chase resolves gives its
# token and value, one it does not is that value's error under its key.

def pt.got_good(+k: String, +x: U32, g: TChase.Got, h: {Theme.th.none(Theme.th.miss(k, g)) == True{} : Bool}) -> {TReader.entry.got(k, x, g) == TReader.Good{Theme.th.ent.got(x, g)} : TReader.EntR}:
  match g:
    case TChase.Hit{v}:
      {==}
    case TChase.Miss{why}:
      themes.pt.absurdF({TReader.entry.got(k, x, TChase.Miss{why}) == TReader.Good{Theme.th.ent.got(x, TChase.Miss{why})} : TReader.EntR}, h)

def pt.entry_good(+vars: List<&2, TFile.Var>, e: TFile.REnt, h: {Theme.th.none(Theme.th.fault(vars, e)) == True{} : Bool}) -> {TReader.entry(vars, e) == TReader.Good{Theme.th.ent(vars, e)} : TReader.EntR}:
  match e:
    case TFile.REnt{+k, t, j}:
      match t:
        case None{}:
          themes.pt.absurdF({TReader.entry(vars, TFile.REnt{k, None{}, j}) == TReader.Good{Theme.th.ent(vars, TFile.REnt{k, None{}, j})} : TReader.EntR}, h)
        case Some{+x}:
          pt.got_good(k, x, TChase.chase(vars, j), h)

def pt.unfault(m: Maybe<&2, TFile.Fault>) -> TFile.Fault:
  match m:
    case None{}:
      TFile.Unknown{""}
    case Some{x}:
      x

# Some{a} == Some{f}: the reader's error a is f
def pt.bad_eq(-a: TFile.Fault, -f: TFile.Fault, h: {Some{a} == Some{f} : Maybe<&2, TFile.Fault>}) -> {TReader.Bad{a} == TReader.Bad{f} : TReader.EntR}:
  Equal.cong(Maybe<&2, TFile.Fault>, TReader.EntR, m => TReader.Bad{pt.unfault(m)}, Some{a}, Some{f}, h)

def pt.MIf(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def pt.none_some(-A: Data, -b: A, -G: Type, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  %e : pt.MIf(A, _, G)
  Unit{}

def pt.got_bad(+k: String, +x: U32, g: TChase.Got, -f: TFile.Fault, h: {Theme.th.miss(k, g) == Some{f} : Maybe<&2, TFile.Fault>}) -> {TReader.entry.got(k, x, g) == TReader.Bad{f} : TReader.EntR}:
  match g:
    case TChase.Hit{v}:
      pt.none_some(TFile.Fault, f, {TReader.entry.got(k, x, TChase.Hit{v}) == TReader.Bad{f} : TReader.EntR}, h)
    case TChase.Miss{why}:
      pt.bad_eq(TFile.InColor{k, why}, f, h)

# an entry with a fault reads to that fault
def pt.entry_bad(+vars: List<&2, TFile.Var>, e: TFile.REnt, -f: TFile.Fault, h: {Theme.th.fault(vars, e) == Some{f} : Maybe<&2, TFile.Fault>}) -> {TReader.entry(vars, e) == TReader.Bad{f} : TReader.EntR}:
  match e:
    case TFile.REnt{+k, t, j}:
      match t:
        case None{}:
          pt.bad_eq(TFile.Unknown{k}, f, h)
        case Some{+x}:
          pt.got_bad(k, x, TChase.chase(vars, j), f, h)

def pt.cons_all(+vars: List<&2, TFile.Var>, x: TFile.REnt, es: List<&2, TFile.Ent>, hg: {Theme.th.none(Theme.th.fault(vars, x)) == True{} : Bool}) -> {TReader.ents.cons(TReader.entry(vars, x), TReader.All{es}) == TReader.All{Theme.th.ent(vars, x) <> es} : TReader.Ents}:
  %Equal.sym(TReader.EntR, TReader.entry(vars, x), TReader.Good{Theme.th.ent(vars, x)}, pt.entry_good(vars, x, hg)) : {TReader.ents.cons(_, TReader.All{es}) == TReader.All{Theme.th.ent(vars, x) <> es} : TReader.Ents}
  {==}

def pt.ents_all(+vars: List<&2, TFile.Var>, +cols: List<&2, TFile.REnt>, +ok: {Theme.th.clean(vars, cols) == True{} : Bool}) -> {TReader.ents(TChase.index(vars), cols) == TReader.All{Theme.th.goods(vars, cols)} : TReader.Ents}:
  match cols:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      +hg = themes.pt.and_l(Theme.th.none(Theme.th.fault(vars, x)), Theme.th.clean(vars, rest), ok)
      +ih = pt.ents_all(vars, rest, themes.pt.and_r(Theme.th.none(Theme.th.fault(vars, x)), Theme.th.clean(vars, rest), ok))
      %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), rest), TReader.All{Theme.th.goods(vars, rest)}, ih) : {TReader.ents.cons(TReader.entry(vars, x), _) == TReader.All{Theme.th.ent(vars, x) <> Theme.th.goods(vars, rest)} : TReader.Ents}
      pt.cons_all(vars, x, Theme.th.goods(vars, rest), hg)

# a file that reads to a fault is rejected with it
def pt.parse_failed(+f: TFile.RFile, -x: TFile.Fault, h: {TReader.read(f) == TReader.Failed{x} : TReader.Read}) -> {TPalette.parse(f) == TPalette.Rejected{x} : TPalette.Parsed}:
  %Equal.sym(TReader.Read, TReader.read(f), TReader.Failed{x}, h) : {TPalette.parse.of(_) == TPalette.Rejected{x} : TPalette.Parsed}
  {==}

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

