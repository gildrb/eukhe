# theme: completing a file into a palette (defaults by light or dark background), parsing it, and the color each token paints

import Base
import ../color.bend as Co
import ./file.bend as TFile
import ./token.bend as TToken
import ./reader.bend as TReader

# Completion
# ----------

def concrete.of(m: Maybe<&2, TFile.Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      TToken.concrete(v)

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
def background(+cols: List<&2, TFile.Ent>, page: Maybe<&2, Co.Rgb>) -> Co.Rgb:
  or_else(Co.Rgb, or(Co.Rgb, concrete.of(TToken.get(cols, 57)), or(Co.Rgb, page, concrete.of(TToken.get(cols, 49)))), at(table.eukhe(), 57n))

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
def fill.k(k: TToken.Role, +cols: List<&2, TFile.Ent>, +bg: Co.Rgb, +t: U32) -> Maybe<&2, TFile.Val>:
  match k:
    case TToken.Req{}:
      TToken.get(cols, t)
    case TToken.MdBody{}:
      or(TFile.Val, TToken.get(cols, t), TToken.get(cols, 9))
    case TToken.RefHeader{}:
      Some{or_else(TFile.Val, TToken.get(cols, t), TFile.Hex{at(defaults(Co.light(bg)), 14n)})}
    case TToken.RefSummary{}:
      Some{or_else(TFile.Val, TToken.get(cols, t), TFile.Hex{at(defaults(Co.light(bg)), 15n)})}
    case TToken.Background{}:
      Some{TFile.Hex{bg}}
    case TToken.Foreground{}:
      Some{TFile.Hex{or_else(Co.Rgb, concrete.of(TToken.get(cols, t)), at(defaults(Co.light(bg)), 58n))}}

def fill(+cols: List<&2, TFile.Ent>, +bg: Co.Rgb, +t: U32) -> Maybe<&2, TFile.Val>:
  fill.k(TToken.kind(t), cols, bg, t)

def fill.map(+cols: List<&2, TFile.Ent>, +bg: Co.Rgb, ts: List<&2, U32>) -> List<&2, Maybe<&2, TFile.Val>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      fill(cols, bg, t) <> fill.map(cols, bg, rest)

def palette.go(+cols: List<&2, TFile.Ent>, page: Maybe<&2, Co.Rgb>) -> List<&2, Maybe<&2, TFile.Val>>:
  fill.map(cols, background(cols, page), TToken.toks())

# the palette of a file: a value per token, in token order
def palette(f: TFile.Th) -> List<&2, Maybe<&2, TFile.Val>>:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      palette.go(cols, page)

# the theme is light: its background's luminance is above one half
def light(f: TFile.Th) -> Bool:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      Co.light(background(cols, page))

def bg(f: TFile.Th) -> Co.Rgb:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      background(cols, page)

def complete(p: List<&2, Maybe<&2, TFile.Val>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{v, rest}:
      Bool.and(Maybe.is_some(&2, TFile.Val, v), complete(rest))

def rename(f: TFile.Th, n: String) -> TFile.Th:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      TFile.Th{n, cols, page, card, info}

# The palette of a file
# ---------------------

def declared.of(m: Maybe<&2, TFile.Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          None{}
        case TFile.Idx{i}:
          None{}
        case TFile.Hex{c}:
          Some{c}

# the file's own background, when it writes it as #rrggbb (the terminal
# UI's onboarding canvas)
def declared(+cols: List<&2, TFile.Ent>) -> Maybe<&2, Co.Rgb>:
  declared.of(TToken.get(cols, 57))

def vals(p: List<&2, Maybe<&2, TFile.Val>>) -> List<&2, TFile.Val>:
  match p:
    case Nil{}:
      Nil{}
    case Con{m, rest}:
      or_else(TFile.Val, m, TFile.Dflt{}) <> vals(rest)

# a theme file parsed: why it is invalid, or its palette (a value per
# token, in token order), whether it is light, its own #rrggbb background,
# and its export page, card and info backgrounds
type Parsed is Data:
  Rejected{f: TFile.Fault}
  Painted{vals: List<&2, TFile.Val>, light: Bool, declared: Maybe<&2, Co.Rgb>, page: Maybe<&2, Co.Rgb>, card: Maybe<&2, Co.Rgb>, info: Maybe<&2, Co.Rgb>}

def parse.th(f: TFile.Th) -> Parsed:
  match f:
    case TFile.Th{name, +cols, +page, card, info}:
      Painted{vals(palette.go(cols, page)), Co.light(background(cols, page)), declared(cols), page, card, info}

def parse.of(r: TReader.Read) -> Parsed:
  match r:
    case TReader.Loaded{th}:
      parse.th(th)
    case TReader.Failed{f}:
      Rejected{f}

# read and complete a theme file
def parse(f: TFile.RFile) -> Parsed:
  parse.of(TReader.read(f))

def paint.canvas.at(surface: Bool) -> Nat:
  match surface:
    case True{}:
      57n
    case False{}:
      58n

def paint.hex(v: TFile.Val) -> Co.Rgb:
  match v:
    case TFile.Hex{c}:
      c
    case _:
      Co.Rgb{0, 0, 0}

def paint.canvas(+p: List<&2, Maybe<&2, TFile.Val>>, surface: Bool) -> Co.Rgb:
  paint.hex(or_else(TFile.Val, or_else(Maybe<&2, TFile.Val>, List.get(&2, Maybe<&2, TFile.Val>, p, paint.canvas.at(surface)), None{}), TFile.Dflt{}))

def paint.val(+p: List<&2, Maybe<&2, TFile.Val>>, +t: U32, v: TFile.Val) -> Co.Rgb:
  match v:
    case TFile.Dflt{}:
      paint.canvas(p, TToken.surface(t))
    case TFile.Idx{i}:
      Co.ansi256(i)
    case TFile.Hex{c}:
      c

# the color token t paints: the terminal default is the background on a
# surface and the foreground (58) elsewhere
def paint(+p: List<&2, Maybe<&2, TFile.Val>>, +t: U32) -> Co.Rgb:
  paint.val(p, t, or_else(TFile.Val, or_else(Maybe<&2, TFile.Val>, List.get(&2, Maybe<&2, TFile.Val>, p, U32.to_nat(t)), None{}), TFile.Dflt{}))
