# theme: the theme rules of crates/eukhe-theme (the one theme file
# validator and the one theme name resolver of the terminal UI and the
# HTML export); laws in LAWS.bend section themes (T1), docs/interface.md Themes.
# The Rust crate decodes the JSON and reads the files; every decision on
# what it read is here: `parse` (a file's palette, or the error the user
# sees) and `pick` (the theme a name resolves to, and the warnings).
#
# A token is its index in crates/eukhe-theme/src/token.rs `Token::ALL`:
#   0 accent 1 border 2 borderAccent 3 borderMuted 4 success 5 error
#   6 warning 7 muted 8 dim 9 text 10 thinkingText 11 userMessageText
#   12 customMessageText 13 customMessageLabel 14 refinementHeader 15 refinementSummary 16 toolTitle 17 toolOutput
#   18 mdBody 19 mdHeading 20 mdLink 21 mdLinkUrl 22 mdCode 23 mdCodeBlock
#   24 mdCodeBlockBorder 25 mdQuote 26 mdQuoteBorder 27 mdHr 28 mdListBullet 29 toolDiffAdded
#   30 toolDiffRemoved 31 toolDiffText 32 toolDiffContext 33 syntaxComment 34 syntaxKeyword 35 syntaxFunction
#   36 syntaxVariable 37 syntaxString 38 syntaxNumber 39 syntaxType 40 syntaxOperator 41 syntaxPunctuation
#   42 effortLow 43 effortHigh 44 contextHigh 45 liftLight 46 liftDark
#   47 bashMode 48 selectedBg 49 userMessageBg 50 customMessageBg 51 toolPendingBg 52 toolSuccessBg
#   53 toolErrorBg 54 toolDiffAddedBg 55 toolDiffRemovedBg 56 toolPanelBg 57 background 58 foreground
# 48..57 are surfaces (the terminal default there is the background); the
# others are ink (the terminal default there is the foreground).

import Base
import ./color.bend as Co

# Theme files
# -----------

# a color after variable resolution: the terminal default (""), an
# xterm-256 index, or #rrggbb
type Val is Data:
  Dflt{}
  Idx{i: U32}
  Hex{c: Co.Rgb}

# a JSON value of a theme file, as the rule reads it: a string, with the
# index of the variable of that name in the file's variables when there is
# one; a number, as JSON writes it; anything else (null, a bool, an array,
# an object), as JSON writes it
type Json is Data:
  JStr{s: String, at: Maybe<&2, Nat>}
  JNum{text: String}
  JOther{text: String}

type Var is Data:
  Var{name: String, val: Json}

# a color entry: its key, the token the key names (None: no token), its
# value
type REnt is Data:
  REnt{key: String, t: Maybe<&2, U32>, val: Json}

# a theme file: its name, its variables and colors (each in key order),
# and its export page, card and info backgrounds
type RFile is Data:
  RFile{name: String, vars: List<&2, Var>, cols: List<&2, REnt>, page: Maybe<&2, Json>, card: Maybe<&2, Json>, info: Maybe<&2, Json>}

type Ent is Data:
  Ent{t: U32, v: Val}

# a file after variable resolution: its colors and the export page, card
# and info backgrounds it sets (None: unset, or set to "")
type Th is Data:
  Th{name: String, cols: List<&2, Ent>, page: Maybe<&2, Co.Rgb>, card: Maybe<&2, Co.Rgb>, info: Maybe<&2, Co.Rgb>}

# Errors
# ------

# why a value is no color: a variable met twice on its chain, a variable
# that does not exist, a malformed #rrggbb, any other value that is no
# color
type Why is Data:
  Circular{name: String}
  NotFound{name: String}
  BadHex{text: String}
  BadValue{text: String}

# the export backgrounds
type Surf is Data:
  OnPage{}
  OnCard{}
  OnInfo{}

# why a theme file is invalid: a color key that names no token, a color
# whose value is no color, the required tokens it does not write (in token
# order), an export background whose value is no color
type Fault is Data:
  Unknown{key: String}
  InColor{key: String, why: Why}
  Missing{ts: List<&2, U32>}
  InExport{at: Surf, why: Why}

# Variables
# ----------

# a value resolved: a color, or why it is none
type Got is Data:
  Hit{v: Val}
  Miss{why: Why}

# one step along a chain of variables, as the rule (LAWS.bend th.next)
# takes it: its end, or the next value to read with the variables met so
# far
type Step is Data:
  Stop{g: Got}
  Go{seen: List<&2, Nat>, j: Json}

# i is in xs (stops at the first hit)
def seen.has(xs: List<&2, Nat>, +i: Nat, hit: Bool) -> Bool:
  match xs:
    case Nil{}:
      hit
    case Con{x, rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          seen.has(rest, i, Nat.is_eq(x, i))

# the value of the variable at index n
def var.val(xs: List<&2, Var>, n: Nat) -> Maybe<&2, Json>:
  match xs n:
    case Nil{} _:
      None{}
    case Con{Var{nm, v}, rest} 0n:
      Some{v}
    case Con{x, rest} 1n+p:
      var.val(rest, p)

def hex.got(m: Maybe<&2, Co.Rgb>, s: String) -> Got:
  match m:
    case None{}:
      Miss{BadHex{s}}
    case Some{c}:
      Hit{Hex{c}}

def num.got(m: Maybe<&2, U32>, text: String) -> Got:
  match m:
    case None{}:
      Miss{BadValue{text}}
    case Some{i}:
      Hit{Idx{i}}

# The variables, indexed
# ----------------------
# The variables sit in a tree split by index (a node keeps the first h of
# its variables on its lo side), so a lookup costs a step per level, not
# a step per variable before it; the variables met so far sit in a tree of
# the same shape. Any split answers as the list does (only the speed
# depends on it): the build halves.

type VT is Data:
  VL{xs: List<&2, Var>}
  VN{h: Nat, lo: VT, hi: VT}

def vt.h(t: VT) -> Nat:
  match t:
    case VL{xs}:
      0n
    case VN{h, lo, hi}:
      h

# the value of variable i, lt telling whether i is below t's split
def vt.get(t: VT, lt: Bool, +i: Nat) -> Maybe<&2, Json>:
  match t:
    case VL{xs}:
      var.val(xs, i)
    case VN{+h, +lo, +hi}:
      match lt:
        case True{}:
          vt.get(lo, Nat.is_lt(i, vt.h(lo)), i)
        case False{}:
          +k = Nat.sub(i, h)
          vt.get(hi, Nat.is_lt(k, vt.h(hi)), k)

# the value of variable i
def vt.at(+t: VT, +i: Nat) -> Maybe<&2, Json>:
  vt.get(t, Nat.is_lt(i, vt.h(t)), i)

# the n variables xs as a tree; small: n is at most 1; fuel bounds the
# depth
def vt.build(fuel: Nat, small: Bool, +xs: List<&2, Var>, +n: Nat) -> VT:
  match fuel:
    case 0n:
      VL{xs}
    case 1n++f:
      match small:
        case True{}:
          VL{xs}
        case False{}:
          +h = Nat.div(n, 2n)
          +r = Nat.sub(n, h)
          VN{h, vt.build(f, Nat.is_le(h, 1n), List.take(&2, Var, xs, h), h), vt.build(f, Nat.is_le(r, 1n), List.drop(&2, Var, xs, h), r)}

type ST is Data:
  SL{xs: List<&2, Nat>}
  SN{h: Nat, lo: ST, hi: ST}

def st.h(t: ST) -> Nat:
  match t:
    case SL{xs}:
      0n
    case SN{h, lo, hi}:
      h

# no variable met, in a tree of t's shape
def st.of(t: VT) -> ST:
  match t:
    case VL{xs}:
      SL{Nil{}}
    case VN{h, lo, hi}:
      SN{h, st.of(lo), st.of(hi)}

# variable i was met, lt telling whether i is below t's split
def st.has(t: ST, lt: Bool, +i: Nat) -> Bool:
  match t:
    case SL{xs}:
      seen.has(xs, i, False{})
    case SN{+h, +lo, +hi}:
      match lt:
        case True{}:
          st.has(lo, Nat.is_lt(i, st.h(lo)), i)
        case False{}:
          +k = Nat.sub(i, h)
          st.has(hi, Nat.is_lt(k, st.h(hi)), k)

def st.mem(+t: ST, +i: Nat) -> Bool:
  st.has(t, Nat.is_lt(i, st.h(t)), i)

# variable i met too, lt telling whether i is below t's split
def st.ins(t: ST, lt: Bool, +i: Nat) -> ST:
  match t:
    case SL{xs}:
      SL{i <> xs}
    case SN{+h, +lo, +hi}:
      match lt:
        case True{}:
          SN{h, st.ins(lo, Nat.is_lt(i, st.h(lo)), i), hi}
        case False{}:
          +k = Nat.sub(i, h)
          SN{h, lo, st.ins(hi, Nat.is_lt(k, st.h(hi)), k)}

def st.add(+t: ST, +i: Nat) -> ST:
  st.ins(t, Nat.is_lt(i, st.h(t)), i)

# one step along a chain of variables over the trees: its end, or the
# next value to read with the variables met so far
type FStep is Data:
  FStop{g: Got}
  FGo{seen: ST, j: Json}

def look.next(m: Maybe<&2, Json>, seen: ST, s: String) -> FStep:
  match m:
    case None{}:
      FStop{Miss{NotFound{s}}}
    case Some{j}:
      FGo{seen, j}

def look.var(looped: Bool, +vt: VT, +seen: ST, s: String, +i: Nat) -> FStep:
  match looped:
    case True{}:
      FStop{Miss{Circular{s}}}
    case False{}:
      look.next(vt.at(vt, i), st.add(seen, i), s)

def look.ref(+vt: VT, +seen: ST, s: String, at: Maybe<&2, Nat>) -> FStep:
  match at:
    case None{}:
      FStop{Miss{NotFound{s}}}
    case Some{+i}:
      look.var(st.mem(seen, i), vt, seen, s, i)

def look.sym(sharp: Bool, +vt: VT, +seen: ST, +s: String, at: Maybe<&2, Nat>) -> FStep:
  match sharp:
    case True{}:
      FStop{hex.got(Co.hex(s), s)}
    case False{}:
      look.ref(vt, seen, s, at)

def look.str(+vt: VT, +seen: ST, s: String, at: Maybe<&2, Nat>) -> FStep:
  match s:
    case SNil{}:
      FStop{Hit{Dflt{}}}
    case SCon{+c, rest}:
      look.sym(Char.is_eq(c, '#'), vt, seen, SCon{c, rest}, at)

# read one value: "" is the terminal default, a #-string a hex color, any
# other string names a variable (met before: a cycle); a number is an
# index; anything else is no color
def look.step(+vt: VT, +seen: ST, j: Json) -> FStep:
  match j:
    case JStr{s, at}:
      look.str(vt, seen, s, at)
    case JNum{+text}:
      FStop{num.got(Co.num(text), text)}
    case JOther{text}:
      FStop{Miss{BadValue{text}}}

# follow the steps for at most fuel of them
def look.walk(fuel: Nat, +vt: VT, fs: FStep) -> Got:
  match fuel:
    case 0n:
      match fs:
        case FStop{g}:
          g
        case FGo{seen, j}:
          Miss{Circular{""}}
    case 1n+f:
      match fs:
        case FStop{g}:
          g
        case FGo{seen, j}:
          look.walk(f, vt, look.step(vt, seen, j))

# a file's variables, indexed: their tree, the empty seen tree of its
# shape, and the steps a chase may take (one more than there are
# variables: each step past the first meets a new variable)
type Ix is Data:
  Ix{vt: VT, seen: ST, fuel: Nat}

def index.of(+vt: VT, n: Nat) -> Ix:
  Ix{vt, st.of(vt), 1n+n}

def index(+vars: List<&2, Var>) -> Ix:
  +n = List.length(&2, Var, vars)
  index.of(vt.build(n, Nat.is_le(n, 1n), vars, n), n)

# the color a value resolves to through the indexed variables
def look(ix: Ix, j: Json) -> Got:
  match ix:
    case Ix{vt, seen, fuel}:
      look.walk(fuel, vt, FGo{seen, j})

# the color a value resolves to through the variables
def chase(+vars: List<&2, Var>, j: Json) -> Got:
  look(index(vars), j)

# Colors
# ------

# an entry read: its token and color, or why the file is invalid
type EntR is Data:
  Good{e: Ent}
  Bad{f: Fault}

def entry.got(key: String, t: U32, g: Got) -> EntR:
  match g:
    case Hit{v}:
      Good{Ent{t, v}}
    case Miss{why}:
      Bad{InColor{key, why}}

# an entry read over the indexed variables
def entry.at(+ix: Ix, e: REnt) -> EntR:
  match e:
    case REnt{key, t, val}:
      match t:
        case None{}:
          Bad{Unknown{key}}
        case Some{x}:
          entry.got(key, x, look(ix, val))

# an entry read
def entry(+vars: List<&2, Var>, e: REnt) -> EntR:
  entry.at(index(vars), e)

# the entries read, or the first one's error
type Ents is Data:
  All{es: List<&2, Ent>}
  Stuck{f: Fault}

def ents.cons(r: EntR, rest: Ents) -> Ents:
  match r rest:
    case Bad{f} _:
      Stuck{f}
    case Good{x} All{es}:
      All{x <> es}
    case Good{x} Stuck{f}:
      Stuck{f}

def ents(+ix: Ix, cols: List<&2, REnt>) -> Ents:
  match cols:
    case Nil{}:
      All{Nil{}}
    case Con{e, rest}:
      ents.cons(entry.at(ix, e), ents(ix, rest))

# Tokens
# ------

type Role is Data:
  Req{}
  MdBody{}
  RefHeader{}
  RefSummary{}
  Background{}
  Foreground{}

def kind.pick(t14: Bool, t15: Bool, t18: Bool, t57: Bool, t58: Bool) -> Role:
  match t14:
    case True{}:
      RefHeader{}
    case False{}:
      match t15:
        case True{}:
          RefSummary{}
        case False{}:
          match t18:
            case True{}:
              MdBody{}
            case False{}:
              match t57:
                case True{}:
                  Background{}
                case False{}:
                  match t58:
                    case True{}:
                      Foreground{}
                    case False{}:
                      Req{}

def kind(+t: U32) -> Role:
  kind.pick(U32.is_eq(t, 14), U32.is_eq(t, 15), U32.is_eq(t, 18), U32.is_eq(t, 57), U32.is_eq(t, 58))

# a surface token (48..57): the terminal default there is the background
def surface(+t: U32) -> Bool:
  Bool.and(U32.is_ge(t, 48), U32.is_le(t, 57))

def toks() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]

def get.pick(hit: Bool, v: Val, other: Maybe<&2, Val>) -> Maybe<&2, Val>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      other

# the value a file gives token t (the first entry for it)
def get(cols: List<&2, Ent>, +t: U32) -> Maybe<&2, Val>:
  match cols:
    case Nil{}:
      None{}
    case Con{Ent{k, v}, rest}:
      get.pick(U32.is_eq(k, t), v, get(rest, t))

def has(+cols: List<&2, Ent>, +t: U32) -> Bool:
  Maybe.is_some(&2, Val, get(cols, t))

# what token t of role k needs of a file: a required token its own entry,
# mdBody its own entry or text's (9); the others nothing
def ok.k(k: Role, +cols: List<&2, Ent>, +t: U32) -> Bool:
  match k:
    case Req{}:
      has(cols, t)
    case MdBody{}:
      Bool.or(has(cols, t), has(cols, 9))
    case RefHeader{}:
      True{}
    case RefSummary{}:
      True{}
    case Background{}:
      True{}
    case Foreground{}:
      True{}

def ok(+cols: List<&2, Ent>, +t: U32) -> Bool:
  ok.k(kind(t), cols, t)

def valid.go(+cols: List<&2, Ent>, ts: List<&2, U32>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, rest}:
      Bool.and(ok(cols, t), valid.go(cols, rest))

# a file is valid when it writes every required token
def valid(f: Th) -> Bool:
  match f:
    case Th{name, cols, page, card, info}:
      valid.go(cols, toks())

# the color a value paints where the terminal cannot be asked; None for
# the terminal default
def concrete(v: Val) -> Maybe<&2, Co.Rgb>:
  match v:
    case Dflt{}:
      None{}
    case Idx{i}:
      Some{Co.ansi256(i)}
    case Hex{c}:
      Some{c}

# Reading a file
# --------------

def required.k(k: Role) -> Bool:
  match k:
    case Req{}:
      True{}
    case MdBody{}:
      False{}
    case RefHeader{}:
      False{}
    case RefSummary{}:
      False{}
    case Background{}:
      False{}
    case Foreground{}:
      False{}

# a token every file must write
def required(+t: U32) -> Bool:
  required.k(kind(t))

def missing.keep(keep: Bool, t: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      t <> rest
    case False{}:
      rest

def missing.go(+cols: List<&2, Ent>, ts: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      missing.keep(Bool.and(required(t), Bool.not(has(cols, t))), t, missing.go(cols, rest))

# the required tokens the colors do not write, in token order
def missing(+cols: List<&2, Ent>) -> List<&2, U32>:
  missing.go(cols, toks())

# an export background read: the color it sets (None: ""), or why the
# file is invalid
type Bg is Data:
  BgOk{c: Maybe<&2, Co.Rgb>}
  BgBad{f: Fault}

def surf.got(at: Surf, g: Got) -> Bg:
  match g:
    case Hit{v}:
      BgOk{concrete(v)}
    case Miss{why}:
      BgBad{InExport{at, why}}

def surf(+ix: Ix, at: Surf, m: Maybe<&2, Json>) -> Bg:
  match m:
    case None{}:
      BgOk{None{}}
    case Some{j}:
      surf.got(at, look(ix, j))

# a theme file read: its resolved colors, or why it is invalid
type Read is Data:
  Loaded{th: Th}
  Failed{f: Fault}

def read.end(name: String, es: List<&2, Ent>, p: Bg, c: Bg, i: Bg) -> Read:
  match p c i:
    case BgBad{f} _ _:
      Failed{f}
    case BgOk{pc} BgBad{f} _:
      Failed{f}
    case BgOk{pc} BgOk{cc} BgBad{f}:
      Failed{f}
    case BgOk{pc} BgOk{cc} BgOk{ic}:
      Loaded{Th{name, es, pc, cc, ic}}

def read.full(name: String, +ix: Ix, es: List<&2, Ent>, miss: List<&2, U32>, page: Maybe<&2, Json>, card: Maybe<&2, Json>, info: Maybe<&2, Json>) -> Read:
  match miss:
    case Nil{}:
      read.end(name, es, surf(ix, OnPage{}, page), surf(ix, OnCard{}, card), surf(ix, OnInfo{}, info))
    case Con{t, rest}:
      Failed{Missing{t <> rest}}

def read.cols(name: String, +ix: Ix, r: Ents, page: Maybe<&2, Json>, card: Maybe<&2, Json>, info: Maybe<&2, Json>) -> Read:
  match r:
    case Stuck{f}:
      Failed{f}
    case All{+es}:
      read.full(name, ix, es, missing(es), page, card, info)

# read a theme file: the colors in key order (the first error wins), then
# the required tokens, then the export page, card and info backgrounds
def read(f: RFile) -> Read:
  match f:
    case RFile{name, vars, cols, page, card, info}:
      +ix = index(vars)
      read.cols(name, ix, ents(ix, cols), page, card, info)

def load.of(r: Read) -> Maybe<&2, Th>:
  match r:
    case Loaded{th}:
      Some{th}
    case Failed{f}:
      None{}

# a theme file that reads, resolved
def load(f: RFile) -> Maybe<&2, Th>:
  load.of(read(f))

# Completion
# ----------

def concrete.of(m: Maybe<&2, Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      concrete(v)

def or(-A: Data, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Maybe<&2, A>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

def or_else(-A: Data, a: Maybe<&2, A>, b: A) -> A:
  match a:
    case None{}:
      b
    case Some{x}:
      x

# token t of a shipped table
def at(xs: List<&2, Co.Rgb>, t: Nat) -> Co.Rgb:
  or_else(Co.Rgb, List.get(&2, Co.Rgb, xs, t), Co.Rgb{0, 0, 0})

def table.eukhe() -> List<&2, Co.Rgb>:
  [Co.Rgb{124, 111, 175}, Co.Rgb{124, 111, 175}, Co.Rgb{124, 111, 175}, Co.Rgb{91, 91, 101},
  Co.Rgb{125, 168, 118}, Co.Rgb{208, 111, 130}, Co.Rgb{245, 158, 11}, Co.Rgb{161, 161, 170},
  Co.Rgb{118, 118, 127}, Co.Rgb{229, 229, 231}, Co.Rgb{139, 139, 148}, Co.Rgb{229, 229, 231},
  Co.Rgb{229, 229, 231}, Co.Rgb{245, 158, 11}, Co.Rgb{149, 117, 205}, Co.Rgb{183, 161, 214},
  Co.Rgb{229, 229, 231}, Co.Rgb{161, 161, 170}, Co.Rgb{216, 216, 220}, Co.Rgb{141, 127, 192},
  Co.Rgb{56, 189, 248}, Co.Rgb{118, 118, 127}, Co.Rgb{200, 200, 205}, Co.Rgb{139, 168, 136},
  Co.Rgb{91, 91, 101}, Co.Rgb{161, 161, 170}, Co.Rgb{91, 91, 101}, Co.Rgb{91, 91, 101},
  Co.Rgb{161, 161, 170}, Co.Rgb{63, 185, 80}, Co.Rgb{248, 81, 73}, Co.Rgb{154, 160, 166},
  Co.Rgb{161, 161, 170}, Co.Rgb{161, 161, 170}, Co.Rgb{56, 189, 248}, Co.Rgb{56, 189, 248},
  Co.Rgb{212, 212, 216}, Co.Rgb{139, 168, 136}, Co.Rgb{245, 158, 11}, Co.Rgb{245, 158, 11},
  Co.Rgb{212, 212, 216}, Co.Rgb{212, 212, 216}, Co.Rgb{124, 111, 175}, Co.Rgb{167, 139, 250},
  Co.Rgb{124, 111, 175}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{125, 168, 118},
  Co.Rgb{34, 34, 38}, Co.Rgb{26, 26, 31}, Co.Rgb{21, 21, 24}, Co.Rgb{16, 16, 21},
  Co.Rgb{14, 21, 16}, Co.Rgb{26, 13, 18}, Co.Rgb{1, 95, 0}, Co.Rgb{94, 0, 0},
  Co.Rgb{13, 13, 16}, Co.Rgb{5, 5, 6}, Co.Rgb{229, 229, 231}]

# the background: the file's own, else its export page, else its
# user-message surface (49), else the default theme's background
def background(+cols: List<&2, Ent>, page: Maybe<&2, Co.Rgb>) -> Co.Rgb:
  or_else(Co.Rgb, or(Co.Rgb, concrete.of(get(cols, 57)), or(Co.Rgb, page, concrete.of(get(cols, 49)))), at(table.eukhe(), 57n))

def table.light() -> List<&2, Co.Rgb>:
  [Co.Rgb{85, 120, 120}, Co.Rgb{79, 117, 157}, Co.Rgb{85, 120, 120}, Co.Rgb{144, 144, 144},
  Co.Rgb{83, 124, 83}, Co.Rgb{170, 85, 85}, Co.Rgb{145, 108, 36}, Co.Rgb{108, 108, 108},
  Co.Rgb{112, 112, 112}, Co.Rgb{0, 0, 0}, Co.Rgb{114, 114, 114}, Co.Rgb{0, 0, 0},
  Co.Rgb{0, 0, 0}, Co.Rgb{126, 87, 194}, Co.Rgb{113, 70, 171}, Co.Rgb{129, 101, 167},
  Co.Rgb{0, 0, 0}, Co.Rgb{108, 108, 108}, Co.Rgb{69, 69, 69}, Co.Rgb{126, 87, 194},
  Co.Rgb{79, 117, 157}, Co.Rgb{112, 112, 112}, Co.Rgb{85, 120, 120}, Co.Rgb{83, 124, 83},
  Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108},
  Co.Rgb{83, 124, 83}, Co.Rgb{83, 124, 83}, Co.Rgb{170, 85, 85}, Co.Rgb{87, 96, 106},
  Co.Rgb{108, 108, 108}, Co.Rgb{0, 128, 0}, Co.Rgb{0, 0, 255}, Co.Rgb{121, 94, 38},
  Co.Rgb{0, 16, 128}, Co.Rgb{163, 21, 21}, Co.Rgb{9, 131, 86}, Co.Rgb{37, 123, 149},
  Co.Rgb{0, 0, 0}, Co.Rgb{0, 0, 0}, Co.Rgb{135, 95, 135}, Co.Rgb{139, 0, 139},
  Co.Rgb{135, 95, 135}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{83, 124, 83},
  Co.Rgb{208, 208, 224}, Co.Rgb{232, 232, 232}, Co.Rgb{237, 231, 246}, Co.Rgb{232, 232, 240},
  Co.Rgb{232, 240, 232}, Co.Rgb{240, 232, 232}, Co.Rgb{218, 251, 225}, Co.Rgb{255, 235, 233},
  Co.Rgb{237, 237, 242}, Co.Rgb{248, 248, 248}, Co.Rgb{0, 0, 0}]

# the builtin whose values fill a file's optional tokens: the default
# theme (eukhe) for a dark background, light for a light one
def defaults(light: Bool) -> List<&2, Co.Rgb>:
  match light:
    case True{}:
      table.light()
    case False{}:
      table.eukhe()

# the value of token t of role k in the file's palette
def fill.k(k: Role, +cols: List<&2, Ent>, +bg: Co.Rgb, +t: U32) -> Maybe<&2, Val>:
  match k:
    case Req{}:
      get(cols, t)
    case MdBody{}:
      or(Val, get(cols, t), get(cols, 9))
    case RefHeader{}:
      Some{or_else(Val, get(cols, t), Hex{at(defaults(Co.light(bg)), 14n)})}
    case RefSummary{}:
      Some{or_else(Val, get(cols, t), Hex{at(defaults(Co.light(bg)), 15n)})}
    case Background{}:
      Some{Hex{bg}}
    case Foreground{}:
      Some{Hex{or_else(Co.Rgb, concrete.of(get(cols, t)), at(defaults(Co.light(bg)), 58n))}}

def fill(+cols: List<&2, Ent>, +bg: Co.Rgb, +t: U32) -> Maybe<&2, Val>:
  fill.k(kind(t), cols, bg, t)

def fill.map(+cols: List<&2, Ent>, +bg: Co.Rgb, ts: List<&2, U32>) -> List<&2, Maybe<&2, Val>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      fill(cols, bg, t) <> fill.map(cols, bg, rest)

def palette.go(+cols: List<&2, Ent>, page: Maybe<&2, Co.Rgb>) -> List<&2, Maybe<&2, Val>>:
  fill.map(cols, background(cols, page), toks())

# the palette of a file: a value per token, in token order
def palette(f: Th) -> List<&2, Maybe<&2, Val>>:
  match f:
    case Th{name, cols, page, card, info}:
      palette.go(cols, page)

# the theme is light: its background's luminance is above one half
def light(f: Th) -> Bool:
  match f:
    case Th{name, cols, page, card, info}:
      Co.light(background(cols, page))

def bg(f: Th) -> Co.Rgb:
  match f:
    case Th{name, cols, page, card, info}:
      background(cols, page)

def complete(p: List<&2, Maybe<&2, Val>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{v, rest}:
      Bool.and(Maybe.is_some(&2, Val, v), complete(rest))

def rename(f: Th, n: String) -> Th:
  match f:
    case Th{name, cols, page, card, info}:
      Th{n, cols, page, card, info}

# The palette of a file
# ---------------------

def declared.of(m: Maybe<&2, Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case Dflt{}:
          None{}
        case Idx{i}:
          None{}
        case Hex{c}:
          Some{c}

# the file's own background, when it writes it as #rrggbb (the terminal
# UI's onboarding canvas)
def declared(+cols: List<&2, Ent>) -> Maybe<&2, Co.Rgb>:
  declared.of(get(cols, 57))

def vals(p: List<&2, Maybe<&2, Val>>) -> List<&2, Val>:
  match p:
    case Nil{}:
      Nil{}
    case Con{m, rest}:
      or_else(Val, m, Dflt{}) <> vals(rest)

# a theme file parsed: why it is invalid, or its palette (a value per
# token, in token order), whether it is light, its own #rrggbb background,
# and its export page, card and info backgrounds
type Parsed is Data:
  Rejected{f: Fault}
  Painted{vals: List<&2, Val>, light: Bool, declared: Maybe<&2, Co.Rgb>, page: Maybe<&2, Co.Rgb>, card: Maybe<&2, Co.Rgb>, info: Maybe<&2, Co.Rgb>}

def parse.th(f: Th) -> Parsed:
  match f:
    case Th{name, +cols, +page, card, info}:
      Painted{vals(palette.go(cols, page)), Co.light(background(cols, page)), declared(cols), page, card, info}

def parse.of(r: Read) -> Parsed:
  match r:
    case Loaded{th}:
      parse.th(th)
    case Failed{f}:
      Rejected{f}

# read and complete a theme file
def parse(f: RFile) -> Parsed:
  parse.of(read(f))

def paint.canvas.at(surface: Bool) -> Nat:
  match surface:
    case True{}:
      57n
    case False{}:
      58n

def paint.hex(v: Val) -> Co.Rgb:
  match v:
    case Hex{c}:
      c
    case _:
      Co.Rgb{0, 0, 0}

def paint.canvas(+p: List<&2, Maybe<&2, Val>>, surface: Bool) -> Co.Rgb:
  paint.hex(or_else(Val, or_else(Maybe<&2, Val>, List.get(&2, Maybe<&2, Val>, p, paint.canvas.at(surface)), None{}), Dflt{}))

def paint.val(+p: List<&2, Maybe<&2, Val>>, +t: U32, v: Val) -> Co.Rgb:
  match v:
    case Dflt{}:
      paint.canvas(p, surface(t))
    case Idx{i}:
      Co.ansi256(i)
    case Hex{c}:
      c

# the color token t paints: the terminal default is the background on a
# surface and the foreground (58) elsewhere
def paint(+p: List<&2, Maybe<&2, Val>>, +t: U32) -> Co.Rgb:
  paint.val(p, t, or_else(Val, or_else(Maybe<&2, Val>, List.get(&2, Maybe<&2, Val>, p, U32.to_nat(t)), None{}), Dflt{}))

# Shipped themes
# --------------
# The color every token of each bundled theme paints (Palette::rgb), as
# the bridge test reads them from crates/eukhe-theme/themes/*.json.

type Shipped is Data:
  Eukhe{}
  Dark{}
  Light{}

def table.dark() -> List<&2, Co.Rgb>:
  [Co.Rgb{138, 190, 183}, Co.Rgb{95, 135, 255}, Co.Rgb{0, 215, 255}, Co.Rgb{101, 101, 101},
  Co.Rgb{181, 189, 104}, Co.Rgb{204, 102, 102}, Co.Rgb{255, 255, 0}, Co.Rgb{150, 150, 150},
  Co.Rgb{129, 129, 129}, Co.Rgb{229, 229, 231}, Co.Rgb{134, 134, 134}, Co.Rgb{229, 229, 231},
  Co.Rgb{229, 229, 231}, Co.Rgb{149, 117, 205}, Co.Rgb{149, 117, 205}, Co.Rgb{183, 161, 214},
  Co.Rgb{229, 229, 231}, Co.Rgb{150, 150, 150}, Co.Rgb{196, 196, 196}, Co.Rgb{178, 148, 187},
  Co.Rgb{129, 162, 190}, Co.Rgb{129, 129, 129}, Co.Rgb{138, 190, 183}, Co.Rgb{181, 189, 104},
  Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150},
  Co.Rgb{138, 190, 183}, Co.Rgb{63, 185, 80}, Co.Rgb{248, 81, 73}, Co.Rgb{154, 160, 166},
  Co.Rgb{150, 150, 150}, Co.Rgb{106, 153, 85}, Co.Rgb{86, 156, 214}, Co.Rgb{220, 220, 170},
  Co.Rgb{156, 220, 254}, Co.Rgb{206, 145, 120}, Co.Rgb{181, 206, 168}, Co.Rgb{78, 201, 176},
  Co.Rgb{212, 212, 212}, Co.Rgb{212, 212, 212}, Co.Rgb{178, 148, 187}, Co.Rgb{209, 131, 232},
  Co.Rgb{178, 148, 187}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{181, 189, 104},
  Co.Rgb{58, 58, 74}, Co.Rgb{52, 53, 65}, Co.Rgb{45, 40, 56}, Co.Rgb{40, 40, 50},
  Co.Rgb{40, 50, 40}, Co.Rgb{60, 40, 40}, Co.Rgb{1, 95, 0}, Co.Rgb{94, 0, 0},
  Co.Rgb{38, 38, 48}, Co.Rgb{24, 24, 30}, Co.Rgb{229, 229, 231}]

def table(s: Shipped) -> List<&2, Co.Rgb>:
  match s:
    case Eukhe{}:
      table.eukhe()
    case Dark{}:
      table.dark()
    case Light{}:
      table.light()

# a foreground token on a background token, and the contrast it needs:
# 9/2 for text, 3/1 for a non-text part (a border, a rule, a level mark)
type Duo is Data:
  Duo{fg: Nat, bg: Nat, num: U32, den: U32}

# every ink token: the text ones on the background (57) at 9/2, the user
# and custom message text (11, 12) on their own surfaces (49, 50) at 9/2,
# the non-text ones (the effort ramp ends among them) on the background
# at 3/1. The lift ends paint no ink: a selection band moves toward them.
def pairs() -> List<&2, Duo>:
  [Duo{9n, 57n, 9, 2}, Duo{58n, 57n, 9, 2}, Duo{18n, 57n, 9, 2}, Duo{7n, 57n, 9, 2},
  Duo{8n, 57n, 9, 2}, Duo{10n, 57n, 9, 2}, Duo{16n, 57n, 9, 2}, Duo{17n, 57n, 9, 2},
  Duo{19n, 57n, 9, 2}, Duo{20n, 57n, 9, 2}, Duo{21n, 57n, 9, 2}, Duo{22n, 57n, 9, 2},
  Duo{23n, 57n, 9, 2}, Duo{25n, 57n, 9, 2}, Duo{28n, 57n, 9, 2}, Duo{4n, 57n, 9, 2},
  Duo{5n, 57n, 9, 2}, Duo{6n, 57n, 9, 2}, Duo{0n, 57n, 9, 2}, Duo{13n, 57n, 9, 2},
  Duo{14n, 57n, 9, 2}, Duo{15n, 57n, 9, 2}, Duo{29n, 57n, 9, 2}, Duo{30n, 57n, 9, 2},
  Duo{31n, 57n, 9, 2}, Duo{32n, 57n, 9, 2}, Duo{33n, 57n, 9, 2}, Duo{34n, 57n, 9, 2},
  Duo{35n, 57n, 9, 2}, Duo{36n, 57n, 9, 2}, Duo{37n, 57n, 9, 2}, Duo{38n, 57n, 9, 2},
  Duo{39n, 57n, 9, 2}, Duo{40n, 57n, 9, 2}, Duo{41n, 57n, 9, 2}, Duo{44n, 57n, 9, 2},
  Duo{11n, 49n, 9, 2}, Duo{12n, 50n, 9, 2}, Duo{1n, 57n, 3, 1}, Duo{2n, 57n, 3, 1},
  Duo{3n, 57n, 3, 1}, Duo{24n, 57n, 3, 1}, Duo{26n, 57n, 3, 1}, Duo{27n, 57n, 3, 1},
  Duo{42n, 57n, 3, 1}, Duo{43n, 57n, 3, 1}, Duo{47n, 57n, 3, 1}]

def meets(+xs: List<&2, Co.Rgb>, p: Duo) -> Bool:
  match p:
    case Duo{fg, bg, num, den}:
      Co.contrast_ge(at(xs, fg), at(xs, bg), num, den)

def legible.go(+xs: List<&2, Co.Rgb>, ps: List<&2, Duo>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      Bool.and(meets(xs, p), legible.go(xs, rest))

def legible(+xs: List<&2, Co.Rgb>) -> Bool:
  legible.go(xs, pairs())

# the status colors: accent, success, warning, error
def status(+xs: List<&2, Co.Rgb>) -> List<&2, Co.Rgb>:
  [at(xs, 0n), at(xs, 4n), at(xs, 6n), at(xs, 5n)]

def to256s(xs: List<&2, Co.Rgb>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Co.to256(x) <> to256s(rest)

def notin(+x: U32, ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(U32.is_ne(x, y), notin(x, rest))

def distinct(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(notin(x, rest), distinct(rest))

# the status colors are pairwise distinct as a 256-color terminal paints
# them (so also as written)
def status_distinct(+xs: List<&2, Co.Rgb>) -> Bool:
  distinct(to256s(status(xs)))

# Name resolution
# ---------------
# The candidates in lookup order: the registered files, the builtins, the
# custom directory's files. A candidate is a theme file (or a builtin) by
# the name it advertises; an invalid file never resolves. id tells the
# candidates apart (the builtins are 0 eukhe, 1 dark, 2 light).

type Cand is Data:
  Cand{name: String, valid: Bool, id: U32}

type Res is Data:
  Res{id: U32, warned: Bool}

def builtins() -> List<&2, Cand>:
  [Cand{"eukhe", True{}, 0}, Cand{"dark", True{}, 1}, Cand{"light", True{}, 2}]

def sources(reg: List<&2, Cand>, custom: List<&2, Cand>) -> List<&2, Cand>:
  List.append(&2, Cand, reg, List.append(&2, Cand, builtins(), custom))

# the default theme
def dflt() -> U32:
  0

# a candidate resolves name n
def names(c: Cand, +n: String) -> Bool:
  match c:
    case Cand{name, valid, id}:
      Bool.and(valid, String.eq(name, n))

def find.pick(hit: Bool, id: U32, other: Res) -> Res:
  match hit:
    case True{}:
      Res{id, False{}}
    case False{}:
      other

def find(src: List<&2, Cand>, +n: String) -> Res:
  match src:
    case Nil{}:
      Res{dflt(), True{}}
    case Con{Cand{name, valid, +id}, rest}:
      find.pick(names(Cand{name, valid, id}, n), id, find(rest, n))

def resolve.name.pick(empty: Bool, src: List<&2, Cand>, +n: String) -> Res:
  match empty:
    case True{}:
      Res{dflt(), False{}}
    case False{}:
      find(src, n)

# resolve name n: the empty name is the default theme; else the first
# candidate that resolves it; else the default theme, with a warning
def resolve.name(src: List<&2, Cand>, +n: String) -> Res:
  resolve.name.pick(String.is_empty(n), src, n)

# some candidate of src resolves n
def hit(src: List<&2, Cand>, +n: String) -> Bool:
  match src:
    case Nil{}:
      False{}
    case Con{c, rest}:
      Bool.or(names(c, n), hit(rest, n))

# The theme a name picks
# ----------------------
# Rust reads every theme file the sources reach (the registered files,
# then the custom directory's), in that order; `pick` decides the rest.

# a theme file the sources reach: a valid one, by the name it advertises,
# from the custom directory or not; or one that did not load, with the
# name it advertises (when it is a theme object) and its file stem (when
# that is text)
type Ld is Data:
  Fine{name: String, custom: Bool}
  Broke{name: Maybe<&2, String>, stem: Maybe<&2, String>}

# the candidate id of the file at index at: after the builtins
def file.id(at: Nat) -> U32:
  U32.from_nat(Nat.add(3n, at))

def same(a: Bool, +b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def cands.keep(keep: Bool, nm: String, +at: Nat, rest: List<&2, Cand>) -> List<&2, Cand>:
  match keep:
    case True{}:
      Cand{nm, True{}, file.id(at)} <> rest
    case False{}:
      rest

def cands.of(l: Ld, +custom: Bool, +at: Nat, rest: List<&2, Cand>) -> List<&2, Cand>:
  match l:
    case Fine{nm, c}:
      cands.keep(same(c, custom), nm, at, rest)
    case Broke{nm, st}:
      rest

# the valid files of one source (custom or registered), in order, as
# candidates; the first is at index at
def cands(ls: List<&2, Ld>, +custom: Bool, +at: Nat) -> List<&2, Cand>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      cands.of(l, custom, at, cands(rest, custom, 1n+at))

# the theme name n resolves to over the files ls
def pick.res(+ls: List<&2, Ld>, +n: String) -> Res:
  resolve.name(sources(cands(ls, False{}, 0n), cands(ls, True{}, 0n)), n)

# A valid file whose name an earlier valid file advertises clashes with
# the first of them (it is never picked). There are few theme files: a
# lookup per file is cheap.

type Clash is Data:
  Clash{at: Nat, winner: Nat}

def first.pick(hit: Bool, at: Nat, other: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{at}
    case False{}:
      other

def fine.named(l: Ld, +n: String) -> Bool:
  match l:
    case Fine{nm, c}:
      String.eq(nm, n)
    case Broke{nm, st}:
      False{}

# the index of the first valid file named n (the first is at index at)
def fine.first(ls: List<&2, Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      first.pick(fine.named(l, n), at, fine.first(rest, n, 1n+at))

def clash.if(same: Bool, w: Nat, at: Nat) -> Maybe<&2, Clash>:
  match same:
    case True{}:
      None{}
    case False{}:
      Some{Clash{at, w}}

def clash.of(m: Maybe<&2, Nat>, +at: Nat) -> Maybe<&2, Clash>:
  match m:
    case None{}:
      None{}
    case Some{+w}:
      clash.if(Nat.is_eq(w, at), w, at)

def clash.at(+all: List<&2, Ld>, l: Ld, +at: Nat) -> Maybe<&2, Clash>:
  match l:
    case Fine{+nm, c}:
      clash.of(fine.first(all, nm, 0n), at)
    case Broke{nm, st}:
      None{}

def clash.cons(m: Maybe<&2, Clash>, rest: List<&2, Clash>) -> List<&2, Clash>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def clashes.go(+all: List<&2, Ld>, ls: List<&2, Ld>, +at: Nat) -> List<&2, Clash>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      clash.cons(clash.at(all, l, at), clashes.go(all, rest, 1n+at))

# every clash, in file order
def clashes(+ls: List<&2, Ld>) -> List<&2, Clash>:
  clashes.go(ls, ls, 0n)

# A name that resolves to no theme warns, with its cause: the first file
# that did not load and advertises the name (or, when it is no theme
# object, is named after it), else none.

def blames.name(m: Maybe<&2, String>, st: Maybe<&2, String>, +n: String) -> Bool:
  match m:
    case Some{x}:
      String.eq(x, n)
    case None{}:
      match st:
        case Some{s}:
          String.eq(s, n)
        case None{}:
          False{}

def blames(l: Ld, +n: String) -> Bool:
  match l:
    case Fine{nm, c}:
      False{}
    case Broke{nm, st}:
      blames.name(nm, st, n)

def cause.go(ls: List<&2, Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      first.pick(blames(l, n), at, cause.go(rest, n, 1n+at))

type Cause is Data:
  FailedAt{at: Nat}
  NoTheme{}

def cause.of(m: Maybe<&2, Nat>) -> Cause:
  match m:
    case None{}:
      NoTheme{}
    case Some{at}:
      FailedAt{at}

def skip.is(m: Maybe<&2, Nat>, +at: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, at)

def broken.keep(keep: Bool, at: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match keep:
    case True{}:
      at <> rest
    case False{}:
      rest

def broken.of(l: Ld, +skip: Maybe<&2, Nat>, +at: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Fine{nm, c}:
      rest
    case Broke{nm, st}:
      broken.keep(Bool.not(skip.is(skip, at)), at, rest)

# the files that did not load, in order, but the one at skip
def broken(ls: List<&2, Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      broken.of(l, skip, at, broken(rest, skip, 1n+at))

# what a name picks: the theme (the candidate id: 0..2 the builtins, 3 + i
# the file at index i), the cause of its warning (none when it does not
# warn), the clashes, and the other files that did not load (each warns)
type Pick is Data:
  Pick{res: Res, cause: Maybe<&2, Cause>, clashes: List<&2, Clash>, broken: List<&2, Nat>}

def pick.warn(warned: Bool, id: U32, +ls: List<&2, Ld>, +n: String) -> Pick:
  match warned:
    case True{}:
      +m = cause.go(ls, n, 0n)
      Pick{Res{id, True{}}, Some{cause.of(m)}, clashes(ls), broken(ls, m, 0n)}
    case False{}:
      Pick{Res{id, False{}}, None{}, clashes(ls), broken(ls, None{}, 0n)}

def pick.go(r: Res, +ls: List<&2, Ld>, +n: String) -> Pick:
  match r:
    case Res{id, warned}:
      pick.warn(warned, id, ls, n)

# resolve name n over the files ls
def pick(+ls: List<&2, Ld>, +n: String) -> Pick:
  pick.go(pick.res(ls, n), ls, n)
