# theme: reading a theme file: its color entries, the missing required tokens and the export backgrounds, or the first fault

import Base
import ../color.bend as Co
import ./file.bend as TFile
import ./chase.bend as TChase
import ./token.bend as TToken

# Colors
# ------

# an entry read: its token and color, or why the file is invalid
type EntR is Data:
  Good{e: TFile.Ent}
  Bad{f: TFile.Fault}

def entry.got(key: String, t: U32, g: TChase.Got) -> EntR:
  match g:
    case TChase.Hit{v}:
      Good{TFile.Ent{t, v}}
    case TChase.Miss{why}:
      Bad{TFile.InColor{key, why}}

# an entry read over the indexed variables
def entry.at(+ix: TChase.Ix, e: TFile.REnt) -> EntR:
  match e:
    case TFile.REnt{key, t, val}:
      match t:
        case None{}:
          Bad{TFile.Unknown{key}}
        case Some{x}:
          entry.got(key, x, TChase.look(ix, val))

# an entry read
def entry(+vars: List<&2, TFile.Var>, e: TFile.REnt) -> EntR:
  entry.at(TChase.index(vars), e)

# the entries read, or the first one's error
type Ents is Data:
  All{es: List<&2, TFile.Ent>}
  Stuck{f: TFile.Fault}

def ents.cons(r: EntR, rest: Ents) -> Ents:
  match r rest:
    case Bad{f} _:
      Stuck{f}
    case Good{x} All{es}:
      All{x <> es}
    case Good{x} Stuck{f}:
      Stuck{f}

def ents(+ix: TChase.Ix, cols: List<&2, TFile.REnt>) -> Ents:
  match cols:
    case Nil{}:
      All{Nil{}}
    case Con{e, rest}:
      ents.cons(entry.at(ix, e), ents(ix, rest))

# Reading a file
# --------------

def required.k(k: TToken.Role) -> Bool:
  match k:
    case TToken.Req{}:
      True{}
    case TToken.MdBody{}:
      False{}
    case TToken.RefHeader{}:
      False{}
    case TToken.RefSummary{}:
      False{}
    case TToken.Background{}:
      False{}
    case TToken.Foreground{}:
      False{}

# a token every file must write
def required(+t: U32) -> Bool:
  required.k(TToken.kind(t))

def missing.keep(keep: Bool, t: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      t <> rest
    case False{}:
      rest

def missing.go(+cols: List<&2, TFile.Ent>, ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      missing.keep(Bool.and(required(t), Bool.not(TToken.has(cols, t))), t, missing.go(cols, rest))

# the required tokens the colors do not write, in token order
def missing(+cols: List<&2, TFile.Ent>) -> List<&2, U32>:
  missing.go(cols, TToken.toks())

# an export background read: the color it sets (None: ""), or why the
# file is invalid
type Bg is Data:
  BgOk{c: Maybe<&2, Co.Rgb>}
  BgBad{f: TFile.Fault}

def surf.got(at: TFile.Surf, g: TChase.Got) -> Bg:
  match g:
    case TChase.Hit{v}:
      BgOk{TToken.concrete(v)}
    case TChase.Miss{why}:
      BgBad{TFile.InExport{at, why}}

def surf(+ix: TChase.Ix, at: TFile.Surf, m: Maybe<&2, TFile.Json>) -> Bg:
  match m:
    case None{}:
      BgOk{None{}}
    case Some{j}:
      surf.got(at, TChase.look(ix, j))

# a theme file read: its resolved colors, or why it is invalid
type Read is Data:
  Loaded{th: TFile.Th}
  Failed{f: TFile.Fault}

def read.end(name: String, es: List<&2, TFile.Ent>, p: Bg, c: Bg, i: Bg) -> Read:
  match p c i:
    case BgBad{f} _ _:
      Failed{f}
    case BgOk{pc} BgBad{f} _:
      Failed{f}
    case BgOk{pc} BgOk{cc} BgBad{f}:
      Failed{f}
    case BgOk{pc} BgOk{cc} BgOk{ic}:
      Loaded{TFile.Th{name, es, pc, cc, ic}}

def read.full(name: String, +ix: TChase.Ix, es: List<&2, TFile.Ent>, miss: List<&2, U32>, page: Maybe<&2, TFile.Json>, card: Maybe<&2, TFile.Json>, info: Maybe<&2, TFile.Json>) -> Read:
  match miss:
    case Nil{}:
      read.end(name, es, surf(ix, TFile.OnPage{}, page), surf(ix, TFile.OnCard{}, card), surf(ix, TFile.OnInfo{}, info))
    case Con{t, rest}:
      Failed{TFile.Missing{t <> rest}}

def read.cols(name: String, +ix: TChase.Ix, r: Ents, page: Maybe<&2, TFile.Json>, card: Maybe<&2, TFile.Json>, info: Maybe<&2, TFile.Json>) -> Read:
  match r:
    case Stuck{f}:
      Failed{f}
    case All{+es}:
      read.full(name, ix, es, missing(es), page, card, info)

# read a theme file: the colors in key order (the first error wins), then
# the required tokens, then the export page, card and info backgrounds
def read(f: TFile.RFile) -> Read:
  match f:
    case TFile.RFile{name, vars, cols, page, card, info}:
      +ix = TChase.index(vars)
      read.cols(name, ix, ents(ix, cols), page, card, info)

def load.of(r: Read) -> Maybe<&2, TFile.Th>:
  match r:
    case Loaded{th}:
      Some{th}
    case Failed{f}:
      None{}

# a theme file that reads, resolved
def load(f: TFile.RFile) -> Maybe<&2, TFile.Th>:
  load.of(read(f))
