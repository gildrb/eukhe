# theme: the bundled themes' painted colors and their legibility and distinct-status checks

import Base
import ../color.bend as Co
import ./palette.bend as TPalette

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
      TPalette.table.eukhe()
    case Dark{}:
      table.dark()
    case Light{}:
      TPalette.table.light()

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
      Co.contrast_ge(TPalette.at(xs, fg), TPalette.at(xs, bg), num, den)

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
  [TPalette.at(xs, 0n), TPalette.at(xs, 4n), TPalette.at(xs, 6n), TPalette.at(xs, 5n)]

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
