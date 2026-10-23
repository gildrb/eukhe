# eukhe: the proof of LAW theme_load_valid

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# Loading and completion
# ----------------------

def themes.pt.some_inj(-A: Data, -a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => TPalette.or_else(A, m, a), Some{a}, Some{b}, e)

def pt.con_nil(-G: Type, -x: U32, -xs: List<&2, U32>, e: {x <> xs == Nil{} : List<&2, U32>}) -> G:
  %e : LLogicLogic.themes.pt.BD(List.is_empty(&2, U32, _), G, Unit)
  Unit{}

# an empty missing list: no keep took its token
def pt.keep_nil(c: Bool, +t: U32, +rest: List<&2, U32>, h: {TReader.missing.keep(c, t, rest) == Nil{} : List<&2, U32>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      pt.con_nil({True{} == False{} : Bool}, t, rest, h)
    case False{}:
      {==}

def pt.keep_rest(c: Bool, +t: U32, +rest: List<&2, U32>, h: {TReader.missing.keep(c, t, rest) == Nil{} : List<&2, U32>}) -> {rest == Nil{} : List<&2, U32>}:
  match c:
    case True{}:
      pt.con_nil({rest == Nil{} : List<&2, U32>}, t, rest, h)
    case False{}:
      h

def pt.not_false(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.themes.pt.absurdT({False{} == True{} : Bool}, h)

def pt.or_true_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a token the missing list does not take is ok, when text is written
def pt.ok_of(k: TToken.Role, +cols: List<&2, TFile.Ent>, +t: U32, +h9: {TToken.has(cols, 9) == True{} : Bool}, +hc: {Bool.and(TReader.required.k(k), Bool.not(TToken.has(cols, t))) == False{} : Bool}) -> {TToken.ok.k(k, cols, t) == True{} : Bool}:
  match k:
    case TToken.Req{}:
      pt.not_false(TToken.has(cols, t), hc)
    case TToken.MdBody{}:
      pt.or_true_r(TToken.has(cols, t), TToken.has(cols, 9), h9)
    case TToken.RefHeader{}:
      {==}
    case TToken.RefSummary{}:
      {==}
    case TToken.Background{}:
      {==}
    case TToken.Foreground{}:
      {==}

def pt.valid_go(+cols: List<&2, TFile.Ent>, +ts: List<&2, U32>, +h9: {TToken.has(cols, 9) == True{} : Bool}, +hm: {TReader.missing.go(cols, ts) == Nil{} : List<&2, U32>}) -> {TToken.valid.go(cols, ts) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      +c = Bool.and(TReader.required(t), Bool.not(TToken.has(cols, t)))
      +more = pt.valid_go(cols, rest, h9, pt.keep_rest(c, t, TReader.missing.go(cols, rest), hm))
      +here = pt.ok_of(TToken.kind(t), cols, t, h9, pt.keep_nil(c, t, TReader.missing.go(cols, rest), hm))
      LA.themes.pt.and_t(TToken.ok(cols, t), TToken.valid.go(cols, rest), here, more)

# a required token at index k of ts is written when the missing list of
# ts is empty
def pt.miss_at(+cols: List<&2, TFile.Ent>, +ts: List<&2, U32>, +k: Nat, +t: U32, +hm: {TReader.missing.go(cols, ts) == Nil{} : List<&2, U32>}, +hg: {List.get(&2, U32, ts, k) == Some{t} : Maybe<&2, U32>}, +hr: {TReader.required(t) == True{} : Bool}) -> {TToken.has(cols, t) == True{} : Bool}:
  match ts k:
    case Nil{} q:
      LLogicLogic.themes.pt.none_some({TToken.has(cols, t) == True{} : Bool}, U32, t, hg)
    case Con{+x, rest} 0n:
      +cx = pt.keep_nil(Bool.and(TReader.required(x), Bool.not(TToken.has(cols, x))), x, TReader.missing.go(cols, rest), hm)
      +ct = {%themes.pt.some_inj(U32, x, t, hg) : {Bool.and(TReader.required(_), Bool.not(TToken.has(cols, _))) == False{} : Bool}; cx : {Bool.and(TReader.required(t), Bool.not(TToken.has(cols, t))) == False{} : Bool}}
      pt.not_false(TToken.has(cols, t), {%hr : {Bool.and(_, Bool.not(TToken.has(cols, t))) == False{} : Bool}; ct : {Bool.not(TToken.has(cols, t)) == False{} : Bool}})
    case Con{+x, rest} 1n+p:
      pt.miss_at(cols, rest, p, t, pt.keep_rest(Bool.and(TReader.required(x), Bool.not(TToken.has(cols, x))), x, TReader.missing.go(cols, rest), hm), hg, hr)

# a file with no missing token is valid
def pt.valid_of(+es: List<&2, TFile.Ent>, +hm: {TReader.missing(es) == Nil{} : List<&2, U32>}) -> {TToken.valid.go(es, TToken.toks()) == True{} : Bool}:
  pt.valid_go(es, TToken.toks(), pt.miss_at(es, TToken.toks(), 9n, 9, hm, {==}, {==}), hm)

def pt.load_end(+name: String, +es: List<&2, TFile.Ent>, p: TReader.Bg, c: TReader.Bg, i: TReader.Bg, -f: TFile.Th, +hv: {TToken.valid.go(es, TToken.toks()) == True{} : Bool}, h: {TReader.load.of(TReader.read.end(name, es, p, c, i)) == Some{f} : Maybe<&2, TFile.Th>}) -> {TToken.valid(f) == True{} : Bool}:
  match p c i:
    case TReader.BgBad{x} q r:
      LLogicLogic.themes.pt.none_some({TToken.valid(f) == True{} : Bool}, TFile.Th, f, h)
    case TReader.BgOk{pc} TReader.BgBad{x} r:
      LLogicLogic.themes.pt.none_some({TToken.valid(f) == True{} : Bool}, TFile.Th, f, h)
    case TReader.BgOk{pc} TReader.BgOk{cc} TReader.BgBad{x}:
      LLogicLogic.themes.pt.none_some({TToken.valid(f) == True{} : Bool}, TFile.Th, f, h)
    case TReader.BgOk{pc} TReader.BgOk{cc} TReader.BgOk{ic}:
      %themes.pt.some_inj(TFile.Th, TFile.Th{name, es, pc, cc, ic}, f, h) : {TToken.valid(_) == True{} : Bool}
      hv

def pt.load_full(+name: String, +ix: TChase.Ix, +es: List<&2, TFile.Ent>, miss: List<&2, U32>, +pg: Maybe<&2, TFile.Json>, +cd: Maybe<&2, TFile.Json>, +io: Maybe<&2, TFile.Json>, -f: TFile.Th, +hm: {TReader.missing(es) == miss : List<&2, U32>}, h: {TReader.load.of(TReader.read.full(name, ix, es, miss, pg, cd, io)) == Some{f} : Maybe<&2, TFile.Th>}) -> {TToken.valid(f) == True{} : Bool}:
  match miss:
    case Nil{}:
      pt.load_end(name, es, TReader.surf(ix, TFile.OnPage{}, pg), TReader.surf(ix, TFile.OnCard{}, cd), TReader.surf(ix, TFile.OnInfo{}, io), f, pt.valid_of(es, hm), h)
    case Con{t, rest}:
      LLogicLogic.themes.pt.none_some({TToken.valid(f) == True{} : Bool}, TFile.Th, f, h)

def pt.load_cols(+name: String, +ix: TChase.Ix, r: TReader.Ents, +pg: Maybe<&2, TFile.Json>, +cd: Maybe<&2, TFile.Json>, +io: Maybe<&2, TFile.Json>, -f: TFile.Th, h: {TReader.load.of(TReader.read.cols(name, ix, r, pg, cd, io)) == Some{f} : Maybe<&2, TFile.Th>}) -> {TToken.valid(f) == True{} : Bool}:
  match r:
    case TReader.Stuck{x}:
      LLogicLogic.themes.pt.none_some({TToken.valid(f) == True{} : Bool}, TFile.Th, f, h)
    case TReader.All{+es}:
      pt.load_full(name, ix, es, TReader.missing(es), pg, cd, io, f, {==}, h)

def theme_load_valid(r: TFile.RFile, -f: TFile.Th, loaded: {TReader.load(r) == Some{f} : Maybe<&2, TFile.Th>}) -> {TToken.valid(f) == True{} : Bool}:
  match r:
    case TFile.RFile{name, vars, cols, page, card, info}:
      +ix = TChase.index(vars)
      pt.load_cols(name, ix, TReader.ents(ix, cols), page, card, info, f, loaded)

def Theme.theme_load_valid(r, f, loaded):
  theme_load_valid(r, f, loaded)
