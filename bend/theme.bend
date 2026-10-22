# theme: the theme model of crates/eukhe-theme (the one theme file
# validator and the one theme name resolver of the terminal UI and the
# HTML export); laws in LAWS.bend section themes (T1), docs/interface.md Themes.
# The bridge test crates/eukhe-core/src/export_html/theme_bridge.rs runs
# the Rust crate and this model (through bend/bridge_theme.bend) on the
# same scenarios.
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

# a value as the file writes it: a color, a malformed color (#abc, 300,
# null), or the name of a variable
type Raw is Data:
  Lit{v: Val}
  Bad{}
  Ref{name: String}

type Var is Data:
  Var{name: String, raw: Raw}

type REnt is Data:
  REnt{t: U32, raw: Raw}

# a theme file: its name, variables, colors and export page background
type RFile is Data:
  RFile{name: String, vars: List<&2, Var>, cols: List<&2, REnt>, page: Maybe<&2, Raw>}

type Ent is Data:
  Ent{t: U32, v: Val}

# a file after variable resolution; page is its export page background
type Th is Data:
  Th{name: String, cols: List<&2, Ent>, page: Maybe<&2, Co.Rgb>}

def var.pick(hit: Bool, raw: Raw, other: Maybe<&2, Raw>) -> Maybe<&2, Raw>:
  match hit:
    case True{}:
      Some{raw}
    case False{}:
      other

def var.get(vars: List<&2, Var>, +n: String) -> Maybe<&2, Raw>:
  match vars:
    case Nil{}:
      None{}
    case Con{Var{name, raw}, rest}:
      var.pick(String.eq(name, n), raw, var.get(rest, n))

# a missing variable is no color
def var.or_bad(m: Maybe<&2, Raw>) -> Raw:
  match m:
    case None{}:
      Bad{}
    case Some{raw}:
      raw

# follow a value through the variables for at most fuel steps: a missing
# variable, a malformed color and a chain longer than the variables (a
# cycle) have no value
def resolve(fuel: Nat, +vars: List<&2, Var>, raw: Raw) -> Maybe<&2, Val>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match raw:
        case Lit{v}:
          Some{v}
        case Bad{}:
          None{}
        case Ref{name}:
          resolve(f, vars, var.or_bad(var.get(vars, name)))

def fuel(vars: List<&2, Var>) -> Nat:
  1n+List.length(&2, Var, vars)

def resolve.cons(t: U32, v: Maybe<&2, Val>, rest: Maybe<&2, List<&2, Ent>>) -> Maybe<&2, List<&2, Ent>>:
  match v rest:
    case Some{x} Some{xs}:
      Some{Ent{t, x} <> xs}
    case _ _:
      None{}

def resolve.cols(+vars: List<&2, Var>, cols: List<&2, REnt>) -> Maybe<&2, List<&2, Ent>>:
  match cols:
    case Nil{}:
      Some{Nil{}}
    case Con{REnt{t, raw}, rest}:
      resolve.cons(t, resolve(fuel(vars), vars, raw), resolve.cols(vars, rest))

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
    case Th{name, cols, page}:
      valid.go(cols, toks())

def load.keep(ok: Bool, f: Th) -> Maybe<&2, Th>:
  match ok:
    case True{}:
      Some{f}
    case False{}:
      None{}

def load.valid(+f: Th) -> Maybe<&2, Th>:
  load.keep(valid(f), f)

def load.check(name: String, cols: Maybe<&2, List<&2, Ent>>, page: Maybe<&2, Maybe<&2, Co.Rgb>>) -> Maybe<&2, Th>:
  match cols page:
    case Some{cs} Some{pg}:
      load.valid(Th{name, cs, pg})
    case _ _:
      None{}

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

def load.page.val(v: Maybe<&2, Val>) -> Maybe<&2, Maybe<&2, Co.Rgb>>:
  match v:
    case None{}:
      None{}
    case Some{x}:
      Some{concrete(x)}

def load.page(+vars: List<&2, Var>, page: Maybe<&2, Raw>) -> Maybe<&2, Maybe<&2, Co.Rgb>>:
  match page:
    case None{}:
      Some{None{}}
    case Some{raw}:
      load.page.val(resolve(fuel(vars), vars, raw))

# read a theme file: every color resolves and the file is valid
def load(f: RFile) -> Maybe<&2, Th>:
  match f:
    case RFile{name, +vars, cols, page}:
      load.check(name, resolve.cols(vars, cols), load.page(vars, page))

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
    case Th{name, cols, page}:
      palette.go(cols, page)

# the theme is light: its background's luminance is above one half
def light(f: Th) -> Bool:
  match f:
    case Th{name, cols, page}:
      Co.light(background(cols, page))

def bg(f: Th) -> Co.Rgb:
  match f:
    case Th{name, cols, page}:
      background(cols, page)

def complete(p: List<&2, Maybe<&2, Val>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{v, rest}:
      Bool.and(Maybe.is_some(&2, Val, v), complete(rest))

def rename(f: Th, n: String) -> Th:
  match f:
    case Th{name, cols, page}:
      Th{n, cols, page}

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
