# tokens: the dashboard's presentation tokens, the model of (T2) in
# laws/tokens.bend. The web app writes the same values once,
# in crates/eukhe-dashboard/ui/src/tokens.stylex.ts; its test
# src/tokens.test.ts runs bridge/bridge_tokens.bend and checks that both
# tables are equal.
#
# 1. The palette. A color token (Tone) has a value in each mode (Light,
#    Dark): an sRGB color and an alpha in hundredths (100: opaque). The
#    tables list the tokens in the order of `lightPalette`.
# 2. Legibility. The pairs that the web app draws as text on a ground,
#    each with the contrast it needs: 4.5:1 for text (WCAG 1.4.3), 3:1
#    for the tertiary captions on the fills (surface, hover), which reach
#    4.0:1 there in the approved look.
# 3. The scales. The stacking layers bottom to top, the spacing steps,
#    the type sizes and the line heights, each with its value in px (the
#    layers: the z-index).
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base
import ./color.bend as Co

# 1. The palette
# --------------

type Mode is Data:
  Light{}
  Dark{}

type Tone is Data:
  Bg{}
  Sidebar{}
  Raised{}
  Surface{}
  Hover{}
  Primary{}
  Secondary{}
  Tertiary{}
  Hairline{}
  Scrim{}
  Danger{}
  Selection{}
  Scrollbar{}
  ShadowNear{}
  ShadowFar{}
  ShadowDrawer{}
  ShadowLatest{}

def Tone.idx(t: Tone) -> U32:
  match t:
    case Bg{}:
      0
    case Sidebar{}:
      1
    case Raised{}:
      2
    case Surface{}:
      3
    case Hover{}:
      4
    case Primary{}:
      5
    case Secondary{}:
      6
    case Tertiary{}:
      7
    case Hairline{}:
      8
    case Scrim{}:
      9
    case Danger{}:
      10
    case Selection{}:
      11
    case Scrollbar{}:
      12
    case ShadowNear{}:
      13
    case ShadowFar{}:
      14
    case ShadowDrawer{}:
      15
    case ShadowLatest{}:
      16

def Tone.eq(a: Tone, b: Tone) -> Bool:
  U32.is_eq(Tone.idx(a), Tone.idx(b))

# the key in tokens.stylex.ts
def Tone.name(t: Tone) -> String:
  match t:
    case Bg{}:
      "bg"
    case Sidebar{}:
      "sidebar"
    case Raised{}:
      "raised"
    case Surface{}:
      "surface"
    case Hover{}:
      "hover"
    case Primary{}:
      "primary"
    case Secondary{}:
      "secondary"
    case Tertiary{}:
      "tertiary"
    case Hairline{}:
      "hairline"
    case Scrim{}:
      "scrim"
    case Danger{}:
      "danger"
    case Selection{}:
      "selection"
    case Scrollbar{}:
      "scrollbar"
    case ShadowNear{}:
      "shadowNear"
    case ShadowFar{}:
      "shadowFar"
    case ShadowDrawer{}:
      "shadowDrawer"
    case ShadowLatest{}:
      "shadowLatest"

def tones() -> List<&2, Tone>:
  [Bg{}, Sidebar{}, Raised{}, Surface{}, Hover{}, Primary{}, Secondary{}, Tertiary{}, Hairline{}, Scrim{}, Danger{}, Selection{}, Scrollbar{}, ShadowNear{}, ShadowFar{}, ShadowDrawer{}, ShadowLatest{}]

# a color and its alpha in hundredths
type Col is Data:
  Col{rgb: Co.Rgb, a: U32}

# a tone's value in one mode
type Entry is Data:
  Entry{tone: Tone, col: Col}

def opaque(r: U32, g: U32, b: U32) -> Col:
  Col{Co.Rgb{r, g, b}, 100}

def tint(r: U32, g: U32, b: U32, a: U32) -> Col:
  Col{Co.Rgb{r, g, b}, a}

def palette(m: Mode) -> List<&2, Entry>:
  match m:
    case Light{}:
      [Entry{Bg{}, opaque(255, 255, 255)}, Entry{Sidebar{}, opaque(249, 249, 249)}, Entry{Raised{}, opaque(255, 255, 255)}, Entry{Surface{}, opaque(244, 244, 244)}, Entry{Hover{}, opaque(236, 236, 236)}, Entry{Primary{}, opaque(13, 13, 13)}, Entry{Secondary{}, opaque(93, 93, 93)}, Entry{Tertiary{}, opaque(115, 115, 115)}, Entry{Hairline{}, tint(0, 0, 0, 10)}, Entry{Scrim{}, tint(0, 0, 0, 20)}, Entry{Danger{}, opaque(196, 39, 27)}, Entry{Selection{}, tint(0, 0, 0, 14)}, Entry{Scrollbar{}, tint(0, 0, 0, 20)}, Entry{ShadowNear{}, tint(0, 0, 0, 6)}, Entry{ShadowFar{}, tint(0, 0, 0, 10)}, Entry{ShadowDrawer{}, tint(0, 0, 0, 20)}, Entry{ShadowLatest{}, tint(0, 0, 0, 12)}]
    case Dark{}:
      [Entry{Bg{}, opaque(33, 33, 33)}, Entry{Sidebar{}, opaque(24, 24, 24)}, Entry{Raised{}, opaque(42, 42, 42)}, Entry{Surface{}, opaque(48, 48, 48)}, Entry{Hover{}, opaque(58, 58, 58)}, Entry{Primary{}, opaque(236, 236, 236)}, Entry{Secondary{}, opaque(180, 180, 180)}, Entry{Tertiary{}, opaque(155, 155, 155)}, Entry{Hairline{}, tint(255, 255, 255, 10)}, Entry{Scrim{}, tint(0, 0, 0, 50)}, Entry{Danger{}, opaque(255, 138, 128)}, Entry{Selection{}, tint(255, 255, 255, 22)}, Entry{Scrollbar{}, tint(255, 255, 255, 20)}, Entry{ShadowNear{}, tint(0, 0, 0, 30)}, Entry{ShadowFar{}, tint(0, 0, 0, 40)}, Entry{ShadowDrawer{}, tint(0, 0, 0, 20)}, Entry{ShadowLatest{}, tint(0, 0, 0, 12)}]

# Some{c} when the entry's tone is the one asked for
def hit(b: Bool, c: Col) -> Maybe<&2, Col>:
  match b:
    case True{}:
      Some{c}
    case False{}:
      None{}

# the value of t in a table (the first entry for it), None when the table has none
def find(+t: Tone, xs: List<&2, Entry>) -> Maybe<&2, Col>:
  match xs:
    case Nil{}:
      None{}
    case Con{Entry{k, c}, rest}:
      Maybe.or(&2, Col, hit(Tone.eq(k, t), c), find(t, rest))

# 2. Legibility
# -------------

# the contrast a pair needs: 9/2 for text (prose), 3/1 for captions on
# fills
type Need is Data:
  Prose{}
  Caption{}

# text in tone fg on ground bg
type Ink is Data:
  Ink{fg: Tone, bg: Tone, need: Need}

def grounds(+fg: Tone, +need: Need) -> List<&2, Ink>:
  [Ink{fg, Bg{}, need}, Ink{fg, Sidebar{}, need}, Ink{fg, Raised{}, need}, Ink{fg, Surface{}, need}, Ink{fg, Hover{}, need}]

# primary, secondary and danger text on every ground; tertiary on the
# grounds, and as a caption on the fills; the ground's color on the
# filled controls (primary: tooltips, the approval card, the send
# button; secondary: a primary button under the pointer; danger: a
# danger button)
def pairs() -> List<&2, Ink>:
  List.concat(&2, Ink, [grounds(Primary{}, Prose{}), grounds(Secondary{}, Prose{}), grounds(Danger{}, Prose{}), [Ink{Tertiary{}, Bg{}, Prose{}}, Ink{Tertiary{}, Sidebar{}, Prose{}}, Ink{Tertiary{}, Raised{}, Prose{}}, Ink{Tertiary{}, Surface{}, Caption{}}, Ink{Tertiary{}, Hover{}, Caption{}}, Ink{Bg{}, Primary{}, Prose{}}, Ink{Bg{}, Secondary{}, Prose{}}, Ink{Bg{}, Danger{}, Prose{}}]])

def Need.num(n: Need) -> U32:
  match n:
    case Prose{}:
      9
    case Caption{}:
      3

def Need.den(n: Need) -> U32:
  match n:
    case Prose{}:
      2
    case Caption{}:
      1

# both colors exist and their contrast meets the need
def meets(fg: Maybe<&2, Col>, bg: Maybe<&2, Col>, +need: Need) -> Bool:
  match fg bg:
    case Some{Col{a, _}} Some{Col{b, _}}:
      Co.contrast_ge(a, b, Need.num(need), Need.den(need))
    case _ _:
      False{}

def readable(+m: Mode, p: Ink) -> Bool:
  Ink{fg, bg, need} = p
  meets(find(fg, palette(m)), find(bg, palette(m)), need)

# every pair of xs is readable in m
def readable.all(+m: Mode, xs: List<&2, Ink>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{p, rest}:
      Bool.and(readable(m, p), readable.all(m, rest))

# 3. The scales
# -------------

# a step of a scale: its key in tokens.stylex.ts and its value
type Step is Data:
  Step{name: String, v: U32}

def layers() -> List<&2, Step>:
  [Step{"topbar", 10}, Step{"latest", 20}, Step{"overlay", 40}, Step{"popover", 50}, Step{"tooltip", 60}, Step{"skip", 70}]

def space() -> List<&2, Step>:
  [Step{"x025", 1}, Step{"x05", 2}, Step{"x1", 4}, Step{"x15", 6}, Step{"x2", 8}, Step{"x25", 10}, Step{"x3", 12}, Step{"x4", 16}, Step{"x5", 20}, Step{"x6", 24}, Step{"x8", 32}, Step{"x12", 48}]

def sizes() -> List<&2, Step>:
  [Step{"tiny", 13}, Step{"small", 14}, Step{"text", 16}, Step{"title", 19}]

def lines() -> List<&2, Step>:
  [Step{"smallLine", 20}, Step{"blockLine", 22}, Step{"textLine", 24}, Step{"proseLine", 26}]

# every value of xs is above v, and each is above the one before it
def ascends.from(xs: List<&2, Step>, +v: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Step{_, +w}, rest}:
      Bool.and(U32.is_lt(v, w), ascends.from(rest, w))

# the values of xs strictly ascend
def ascends(xs: List<&2, Step>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Step{_, v}, rest}:
      ascends.from(rest, v)
