# eukhe: lemmas the proofs of the completion laws of area theme share
# (theme_parse_*): the parse of a file that reads, the value at a place of
# the palette, the role of the tokens below the background, the builtin of
# a mode, the background's fallbacks.

import Base
import ../../../bend/color.bend as Co
import ../../../bend/theme/bundled.bend as TBundled
import ../../../bend/theme/file.bend as TFile
import ../../../bend/theme/palette.bend as TPalette
import ../../../bend/theme/reader.bend as TReader
import ../../../bend/theme/token.bend as TToken
import ../../../laws/theme.bend as Theme
import ../base.bend as LA

# The parse
# ---------

# the parse of a file that reads: its palette over the background it
# completes to, its mode, its own background, its export backgrounds
def pp.parsed(+cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, cd: Maybe<&2, Co.Rgb>, io: Maybe<&2, Co.Rgb>) -> TPalette.Parsed:
  +b = TPalette.background(cols, pg)
  TPalette.Painted{TPalette.vals(TPalette.fill.map(cols, b, TToken.toks())), Co.light(b), TPalette.declared(cols), pg, cd, io}

def pp.painted(+f: TFile.RFile, +nm: String, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}) -> {TPalette.parse(f) == pp.parsed(cols, pg, cd, io) : TPalette.Parsed}:
  %Equal.sym(TReader.Read, TReader.read(f), TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}}, h) : {TPalette.parse.of(_) == pp.parsed(cols, pg, cd, io) : TPalette.Parsed}
  {==}

# The value at a place
# --------------------

# the n tokens k, k + 1, ...
def pp.upto(n: Nat, +k: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      U32.from_nat(k) <> pp.upto(m, 1n+k)

def pp.toks() -> {TToken.toks() == pp.upto(59n, 0n) : List<&2, U32>}:
  {==}

def pp.add0(k: Nat) -> {k == Nat.add(k, 0n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, p, Nat.add(p, 0n), pp.add0(p))

def pp.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pp.add_succ(p, b))

def pp.lt_succ(i: Nat, n: Nat, h: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(i, 1n+n) == True{} : Bool}:
  match i n:
    case 0n 0n:
      LA.themes.pt.absurdF({Nat.is_lt(0n, 1n+0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LA.themes.pt.absurdF({Nat.is_lt(1n+p, 1n+0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pp.lt_succ(p, q, h)

# the value at place i of the palette of the tokens k, k + 1, ...: token
# k + i's value, the terminal default when unset
def pp.get(+cols: List<&2, TFile.Ent>, +bg: Co.Rgb, n: Nat, +k: Nat, i: Nat, lt: {Nat.is_lt(i, n) == True{} : Bool})
  -> {List.get(&2, TFile.Val, TPalette.vals(TPalette.fill.map(cols, bg, pp.upto(n, k))), i) == Some{TPalette.or_else(TFile.Val, TPalette.fill(cols, bg, U32.from_nat(Nat.add(k, i))), TFile.Dflt{})} : Maybe<&2, TFile.Val>}:
  match n i:
    case 0n 0n:
      LA.themes.pt.absurdF({List.get(&2, TFile.Val, TPalette.vals(TPalette.fill.map(cols, bg, pp.upto(0n, k))), 0n) == Some{TPalette.or_else(TFile.Val, TPalette.fill(cols, bg, U32.from_nat(Nat.add(k, 0n))), TFile.Dflt{})} : Maybe<&2, TFile.Val>}, lt)
    case 0n 1n+q:
      LA.themes.pt.absurdF({List.get(&2, TFile.Val, TPalette.vals(TPalette.fill.map(cols, bg, pp.upto(0n, k))), 1n+q) == Some{TPalette.or_else(TFile.Val, TPalette.fill(cols, bg, U32.from_nat(Nat.add(k, 1n+q))), TFile.Dflt{})} : Maybe<&2, TFile.Val>}, lt)
    case 1n+m 0n:
      %pp.add0(k) : {List.get(&2, TFile.Val, TPalette.vals(TPalette.fill.map(cols, bg, pp.upto(1n+m, k))), 0n) == Some{TPalette.or_else(TFile.Val, TPalette.fill(cols, bg, U32.from_nat(_)), TFile.Dflt{})} : Maybe<&2, TFile.Val>}
      {==}
    case 1n+m 1n+p:
      %Equal.sym(Nat, Nat.add(k, 1n+p), 1n+Nat.add(k, p), pp.add_succ(k, p)) : {List.get(&2, TFile.Val, TPalette.vals(TPalette.fill.map(cols, bg, pp.upto(1n+m, k))), 1n+p) == Some{TPalette.or_else(TFile.Val, TPalette.fill(cols, bg, U32.from_nat(_)), TFile.Dflt{})} : Maybe<&2, TFile.Val>}
      pp.get(cols, bg, m, 1n+k, p, lt)

# The tokens below the background
# -------------------------------
# Every token below 57 is ink or a surface other than the background:
# none is the background or the foreground (a finite check, computed once).

def pp.ink(r: TToken.Role) -> Bool:
  match r:
    case TToken.Req{}:
      True{}
    case TToken.MdBody{}:
      True{}
    case TToken.RefHeader{}:
      True{}
    case TToken.RefSummary{}:
      True{}
    case TToken.Background{}:
      False{}
    case TToken.Foreground{}:
      False{}

def pp.inks(n: Nat, +k: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(pp.ink(TToken.kind(U32.from_nat(k))), pp.inks(m, 1n+k))

def pp.inks57() -> {pp.inks(57n, 0n) == True{} : Bool}:
  {==}

def pp.ink_at(n: Nat, +k: Nat, i: Nat, +h: {pp.inks(n, k) == True{} : Bool}, lt: {Nat.is_lt(i, n) == True{} : Bool}) -> {pp.ink(TToken.kind(U32.from_nat(Nat.add(k, i)))) == True{} : Bool}:
  match n i:
    case 0n 0n:
      LA.themes.pt.absurdF({pp.ink(TToken.kind(U32.from_nat(Nat.add(k, 0n)))) == True{} : Bool}, lt)
    case 0n 1n+q:
      LA.themes.pt.absurdF({pp.ink(TToken.kind(U32.from_nat(Nat.add(k, 1n+q)))) == True{} : Bool}, lt)
    case 1n++m 0n:
      %pp.add0(k) : {pp.ink(TToken.kind(U32.from_nat(_))) == True{} : Bool}
      LA.themes.pt.and_l(pp.ink(TToken.kind(U32.from_nat(k))), pp.inks(m, 1n+k), h)
    case 1n++m 1n+p:
      %Equal.sym(Nat, Nat.add(k, 1n+p), 1n+Nat.add(k, p), pp.add_succ(k, p)) : {pp.ink(TToken.kind(U32.from_nat(_))) == True{} : Bool}
      pp.ink_at(m, 1n+k, p, LA.themes.pt.and_r(pp.ink(TToken.kind(U32.from_nat(k))), pp.inks(m, 1n+k), h), lt)

# a token of an ink role keeps the value the file writes
def pp.fill_ink(r: TToken.Role, +cols: List<&2, TFile.Ent>, +bg: Co.Rgb, +t: U32, -v: TFile.Val, hr: {pp.ink(r) == True{} : Bool}, hg: {TToken.get(cols, t) == Some{v} : Maybe<&2, TFile.Val>}) -> {TPalette.fill.k(r, cols, bg, t) == Some{v} : Maybe<&2, TFile.Val>}:
  match r:
    case TToken.Req{}:
      hg
    case TToken.MdBody{}:
      %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(cols, t), Some{v}, hg) : {TPalette.or(TFile.Val, _, TToken.get(cols, 9)) == Some{v} : Maybe<&2, TFile.Val>}
      {==}
    case TToken.RefHeader{}:
      %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(cols, t), Some{v}, hg) : {Some{TPalette.or_else(TFile.Val, _, TFile.Hex{TPalette.at(TPalette.defaults(Co.light(bg)), 14n)})} == Some{v} : Maybe<&2, TFile.Val>}
      {==}
    case TToken.RefSummary{}:
      %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(cols, t), Some{v}, hg) : {Some{TPalette.or_else(TFile.Val, _, TFile.Hex{TPalette.at(TPalette.defaults(Co.light(bg)), 15n)})} == Some{v} : Maybe<&2, TFile.Val>}
      {==}
    case TToken.Background{}:
      LA.themes.pt.absurdF({TPalette.fill.k(TToken.Background{}, cols, bg, t) == Some{v} : Maybe<&2, TFile.Val>}, hr)
    case TToken.Foreground{}:
      LA.themes.pt.absurdF({TPalette.fill.k(TToken.Foreground{}, cols, bg, t) == Some{v} : Maybe<&2, TFile.Val>}, hr)

# The builtin of a mode
# ---------------------

def pp.at_hexs(m: Maybe<&2, Co.Rgb>, h: {Maybe.is_some(&2, Co.Rgb, m) == True{} : Bool}) -> {Some{TFile.Hex{TPalette.or_else(Co.Rgb, m, Co.Rgb{0, 0, 0})}} == Theme.th.hexs(m) : Maybe<&2, TFile.Val>}:
  match m:
    case None{}:
      LA.themes.pt.absurdF({Some{TFile.Hex{TPalette.or_else(Co.Rgb, None{}, Co.Rgb{0, 0, 0})}} == Theme.th.hexs(None{}) : Maybe<&2, TFile.Val>}, h)
    case Some{c}:
      {==}

# token k of the builtin the code fills a mode from is the laws' builtin
# of that mode (the tables have token k)
def pp.mode(b: Bool, +k: Nat, hl: {Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, TPalette.table.light(), k)) == True{} : Bool}, he: {Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, TPalette.table.eukhe(), k)) == True{} : Bool})
  -> {Some{TFile.Hex{TPalette.at(TPalette.defaults(b), k)}} == Theme.th.builtin.val(b, k) : Maybe<&2, TFile.Val>}:
  match b:
    case True{}:
      pp.at_hexs(List.get(&2, Co.Rgb, TPalette.table.light(), k), hl)
    case False{}:
      pp.at_hexs(List.get(&2, Co.Rgb, TPalette.table.eukhe(), k), he)

# The background's fallbacks
# --------------------------

def pp.paints(m: Maybe<&2, TFile.Val>) -> {TPalette.concrete.of(m) == Theme.th.paints(m) : Maybe<&2, Co.Rgb>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          {==}
        case TFile.Idx{i}:
          {==}
        case TFile.Hex{c}:
          {==}

# the color a written value paints, as the code computes it
def pp.conc(+m: Maybe<&2, TFile.Val>, -r: Maybe<&2, Co.Rgb>, h: {Theme.th.paints(m) == r : Maybe<&2, Co.Rgb>}) -> {r == TPalette.concrete.of(m) : Maybe<&2, Co.Rgb>}:
  Equal.sym(Maybe<&2, Co.Rgb>, TPalette.concrete.of(m), r, Equal.trans(Maybe<&2, Co.Rgb>, TPalette.concrete.of(m), Theme.th.paints(m), r, pp.paints(m), h))

def pp.bg_own(+cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +c: Co.Rgb, h: {Theme.th.paints(TToken.get(cols, 57)) == Some{c} : Maybe<&2, Co.Rgb>}) -> {TPalette.background(cols, pg) == c : Co.Rgb}:
  %pp.conc(TToken.get(cols, 57), Some{c}, h) : {TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, _, TPalette.or(Co.Rgb, pg, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TPalette.table.eukhe(), 57n)) == c : Co.Rgb}
  {==}

def pp.bg_page(+cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +c: Co.Rgb, h1: {Theme.th.paints(TToken.get(cols, 57)) == None{} : Maybe<&2, Co.Rgb>}, h2: {pg == Some{c} : Maybe<&2, Co.Rgb>}) -> {TPalette.background(cols, pg) == c : Co.Rgb}:
  %pp.conc(TToken.get(cols, 57), None{}, h1) : {TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, _, TPalette.or(Co.Rgb, pg, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TPalette.table.eukhe(), 57n)) == c : Co.Rgb}
  %Equal.sym(Maybe<&2, Co.Rgb>, pg, Some{c}, h2) : {TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, None{}, TPalette.or(Co.Rgb, _, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TPalette.table.eukhe(), 57n)) == c : Co.Rgb}
  {==}

def pp.bg_user(+cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +c: Co.Rgb, h1: {Theme.th.paints(TToken.get(cols, 57)) == None{} : Maybe<&2, Co.Rgb>}, h2: {pg == None{} : Maybe<&2, Co.Rgb>}, h3: {Theme.th.paints(TToken.get(cols, 49)) == Some{c} : Maybe<&2, Co.Rgb>}) -> {TPalette.background(cols, pg) == c : Co.Rgb}:
  %pp.conc(TToken.get(cols, 57), None{}, h1) : {TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, _, TPalette.or(Co.Rgb, pg, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TPalette.table.eukhe(), 57n)) == c : Co.Rgb}
  %Equal.sym(Maybe<&2, Co.Rgb>, pg, None{}, h2) : {TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, None{}, TPalette.or(Co.Rgb, _, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TPalette.table.eukhe(), 57n)) == c : Co.Rgb}
  %pp.conc(TToken.get(cols, 49), Some{c}, h3) : {TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, None{}, TPalette.or(Co.Rgb, None{}, _)), TPalette.at(TPalette.table.eukhe(), 57n)) == c : Co.Rgb}
  {==}

def pp.bg_dflt(+cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, h1: {Theme.th.paints(TToken.get(cols, 57)) == None{} : Maybe<&2, Co.Rgb>}, h2: {pg == None{} : Maybe<&2, Co.Rgb>}, h3: {Theme.th.paints(TToken.get(cols, 49)) == None{} : Maybe<&2, Co.Rgb>}) -> {Some{TFile.Hex{TPalette.background(cols, pg)}} == Theme.th.builtin.val(False{}, 57n) : Maybe<&2, TFile.Val>}:
  %pp.conc(TToken.get(cols, 57), None{}, h1) : {Some{TFile.Hex{TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, _, TPalette.or(Co.Rgb, pg, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TPalette.table.eukhe(), 57n))}} == Theme.th.builtin.val(False{}, 57n) : Maybe<&2, TFile.Val>}
  %Equal.sym(Maybe<&2, Co.Rgb>, pg, None{}, h2) : {Some{TFile.Hex{TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, None{}, TPalette.or(Co.Rgb, _, TPalette.concrete.of(TToken.get(cols, 49)))), TPalette.at(TPalette.table.eukhe(), 57n))}} == Theme.th.builtin.val(False{}, 57n) : Maybe<&2, TFile.Val>}
  %pp.conc(TToken.get(cols, 49), None{}, h3) : {Some{TFile.Hex{TPalette.or_else(Co.Rgb, TPalette.or(Co.Rgb, None{}, TPalette.or(Co.Rgb, None{}, _)), TPalette.at(TPalette.table.eukhe(), 57n))}} == Theme.th.builtin.val(False{}, 57n) : Maybe<&2, TFile.Val>}
  {==}
