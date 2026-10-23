# eukhe: the proof of LAW theme_load_valid

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ../base/bool/misc.bend as LBoolMisc
import ../base/maybe.bend as LMaybe
import ./base.bend as LA

# Loading and completion
# ----------------------

def themes.pt.some_inj(-A: Data, -a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => T.or_else(A, m, a), Some{a}, Some{b}, e)

def pt.con_nil(-G: Type, -x: U32, -xs: List<&2, U32>, e: {x <> xs == Nil{} : List<&2, U32>}) -> G:
  %e : LBoolMisc.themes.pt.BD(List.is_empty(&2, U32, _), G, Unit)
  Unit{}

# an empty missing list: no keep took its token
def pt.keep_nil(c: Bool, +t: U32, +rest: List<&2, U32>, h: {T.missing.keep(c, t, rest) == Nil{} : List<&2, U32>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      pt.con_nil({True{} == False{} : Bool}, t, rest, h)
    case False{}:
      {==}

def pt.keep_rest(c: Bool, +t: U32, +rest: List<&2, U32>, h: {T.missing.keep(c, t, rest) == Nil{} : List<&2, U32>}) -> {rest == Nil{} : List<&2, U32>}:
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
def pt.ok_of(k: T.Role, +cols: List<&2, T.Ent>, +t: U32, +h9: {T.has(cols, 9) == True{} : Bool}, +hc: {Bool.and(T.required.k(k), Bool.not(T.has(cols, t))) == False{} : Bool}) -> {T.ok.k(k, cols, t) == True{} : Bool}:
  match k:
    case T.Req{}:
      pt.not_false(T.has(cols, t), hc)
    case T.MdBody{}:
      pt.or_true_r(T.has(cols, t), T.has(cols, 9), h9)
    case T.RefHeader{}:
      {==}
    case T.RefSummary{}:
      {==}
    case T.Background{}:
      {==}
    case T.Foreground{}:
      {==}

def pt.valid_go(+cols: List<&2, T.Ent>, +ts: List<&2, U32>, +h9: {T.has(cols, 9) == True{} : Bool}, +hm: {T.missing.go(cols, ts) == Nil{} : List<&2, U32>}) -> {T.valid.go(cols, ts) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      +c = Bool.and(T.required(t), Bool.not(T.has(cols, t)))
      +more = pt.valid_go(cols, rest, h9, pt.keep_rest(c, t, T.missing.go(cols, rest), hm))
      +here = pt.ok_of(T.kind(t), cols, t, h9, pt.keep_nil(c, t, T.missing.go(cols, rest), hm))
      LA.themes.pt.and_t(T.ok(cols, t), T.valid.go(cols, rest), here, more)

# a required token at index k of ts is written when the missing list of
# ts is empty
def pt.miss_at(+cols: List<&2, T.Ent>, +ts: List<&2, U32>, +k: Nat, +t: U32, +hm: {T.missing.go(cols, ts) == Nil{} : List<&2, U32>}, +hg: {List.get(&2, U32, ts, k) == Some{t} : Maybe<&2, U32>}, +hr: {T.required(t) == True{} : Bool}) -> {T.has(cols, t) == True{} : Bool}:
  match ts k:
    case Nil{} q:
      LMaybe.themes.pt.none_some({T.has(cols, t) == True{} : Bool}, U32, t, hg)
    case Con{+x, rest} 0n:
      +cx = pt.keep_nil(Bool.and(T.required(x), Bool.not(T.has(cols, x))), x, T.missing.go(cols, rest), hm)
      +ct = {%themes.pt.some_inj(U32, x, t, hg) : {Bool.and(T.required(_), Bool.not(T.has(cols, _))) == False{} : Bool}; cx : {Bool.and(T.required(t), Bool.not(T.has(cols, t))) == False{} : Bool}}
      pt.not_false(T.has(cols, t), {%hr : {Bool.and(_, Bool.not(T.has(cols, t))) == False{} : Bool}; ct : {Bool.not(T.has(cols, t)) == False{} : Bool}})
    case Con{+x, rest} 1n+p:
      pt.miss_at(cols, rest, p, t, pt.keep_rest(Bool.and(T.required(x), Bool.not(T.has(cols, x))), x, T.missing.go(cols, rest), hm), hg, hr)

# a file with no missing token is valid
def pt.valid_of(+es: List<&2, T.Ent>, +hm: {T.missing(es) == Nil{} : List<&2, U32>}) -> {T.valid.go(es, T.toks()) == True{} : Bool}:
  pt.valid_go(es, T.toks(), pt.miss_at(es, T.toks(), 9n, 9, hm, {==}, {==}), hm)

def pt.load_end(+name: String, +es: List<&2, T.Ent>, p: T.Bg, c: T.Bg, i: T.Bg, -f: T.Th, +hv: {T.valid.go(es, T.toks()) == True{} : Bool}, h: {T.load.of(T.read.end(name, es, p, c, i)) == Some{f} : Maybe<&2, T.Th>}) -> {T.valid(f) == True{} : Bool}:
  match p c i:
    case T.BgBad{x} q r:
      LMaybe.themes.pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)
    case T.BgOk{pc} T.BgBad{x} r:
      LMaybe.themes.pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)
    case T.BgOk{pc} T.BgOk{cc} T.BgBad{x}:
      LMaybe.themes.pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)
    case T.BgOk{pc} T.BgOk{cc} T.BgOk{ic}:
      %themes.pt.some_inj(T.Th, T.Th{name, es, pc, cc, ic}, f, h) : {T.valid(_) == True{} : Bool}
      hv

def pt.load_full(+name: String, +ix: T.Ix, +es: List<&2, T.Ent>, miss: List<&2, U32>, +pg: Maybe<&2, T.Json>, +cd: Maybe<&2, T.Json>, +io: Maybe<&2, T.Json>, -f: T.Th, +hm: {T.missing(es) == miss : List<&2, U32>}, h: {T.load.of(T.read.full(name, ix, es, miss, pg, cd, io)) == Some{f} : Maybe<&2, T.Th>}) -> {T.valid(f) == True{} : Bool}:
  match miss:
    case Nil{}:
      pt.load_end(name, es, T.surf(ix, T.OnPage{}, pg), T.surf(ix, T.OnCard{}, cd), T.surf(ix, T.OnInfo{}, io), f, pt.valid_of(es, hm), h)
    case Con{t, rest}:
      LMaybe.themes.pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)

def pt.load_cols(+name: String, +ix: T.Ix, r: T.Ents, +pg: Maybe<&2, T.Json>, +cd: Maybe<&2, T.Json>, +io: Maybe<&2, T.Json>, -f: T.Th, h: {T.load.of(T.read.cols(name, ix, r, pg, cd, io)) == Some{f} : Maybe<&2, T.Th>}) -> {T.valid(f) == True{} : Bool}:
  match r:
    case T.Stuck{x}:
      LMaybe.themes.pt.none_some({T.valid(f) == True{} : Bool}, T.Th, f, h)
    case T.All{+es}:
      pt.load_full(name, ix, es, T.missing(es), pg, cd, io, f, {==}, h)

def theme_load_valid(r: T.RFile, -f: T.Th, loaded: {T.load(r) == Some{f} : Maybe<&2, T.Th>}) -> {T.valid(f) == True{} : Bool}:
  match r:
    case T.RFile{name, vars, cols, page, card, info}:
      +ix = T.index(vars)
      pt.load_cols(name, ix, T.ents(ix, cols), page, card, info, f, loaded)

def Theme.theme_load_valid(r, f, loaded):
  theme_load_valid(r, f, loaded)
