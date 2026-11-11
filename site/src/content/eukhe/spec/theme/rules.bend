# theme_rules (spec): the meaning of the theme model's helpers that the
# laws of area theme read (laws/theme.bend, section "The rules' helpers,
# pinned"): which candidate advertises a name, the color a value paints,
# the contrast pairs of the shipped themes and when a table is legible,
# and when its status colors are distinct. A spec: the shipped code never
# calls it.

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/name.bend as TName
import ../../bend/theme/bundled.bend as TBundled

# Names
# -----

# some valid candidate of src advertises exactly the name n
def has(src: List<&2, TName.Cand>, +n: String) -> Bool:
  match src:
    case Nil{}:
      False{}
    case Con{c, rest}:
      match c:
        case TName.Cand{nm, v, id}:
          Bool.or(Bool.and(v, String.eq(nm, n)), has(rest, n))

# Values
# ------

# the color a value paints where the terminal cannot be asked: none for
# the terminal default, an index's xterm-256 color, a written color itself
def concrete(v: TFile.Val) -> Maybe<&2, Co.Rgb>:
  match v:
    case TFile.Dflt{}:
      None{}
    case TFile.Idx{i}:
      Some{Co.ansi256(i)}
    case TFile.Hex{c}:
      Some{c}

# Shipped tables
# --------------

# token k of a table (black past its end)
def get(xs: List<&2, Co.Rgb>, k: Nat) -> Co.Rgb:
  match xs k:
    case Nil{} _:
      Co.Rgb{0, 0, 0}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      get(t, p)

# the contrast every ink token needs: the text tokens (text, foreground,
# mdBody, muted, dim, thinkingText, toolTitle, toolOutput, mdHeading,
# mdLink, mdLinkUrl, mdCode, mdCodeBlock, mdQuote, mdListBullet, success,
# error, warning, accent, customMessageLabel, the refinement pair, the
# diff and syntax tokens, contextHigh) on the background (57) at 9/2; the
# user and custom message texts (11, 12) on their own surfaces (49, 50) at
# 9/2; the non-text parts (the borders, mdCodeBlockBorder, mdQuoteBorder,
# mdHr, the effort ramp ends, bashMode) on the background at 3/1
def pairs() -> List<&2, TBundled.Duo>:
  [TBundled.Duo{9n, 57n, 9, 2}, TBundled.Duo{58n, 57n, 9, 2}, TBundled.Duo{18n, 57n, 9, 2}, TBundled.Duo{7n, 57n, 9, 2},
  TBundled.Duo{8n, 57n, 9, 2}, TBundled.Duo{10n, 57n, 9, 2}, TBundled.Duo{16n, 57n, 9, 2}, TBundled.Duo{17n, 57n, 9, 2},
  TBundled.Duo{19n, 57n, 9, 2}, TBundled.Duo{20n, 57n, 9, 2}, TBundled.Duo{21n, 57n, 9, 2}, TBundled.Duo{22n, 57n, 9, 2},
  TBundled.Duo{23n, 57n, 9, 2}, TBundled.Duo{25n, 57n, 9, 2}, TBundled.Duo{28n, 57n, 9, 2}, TBundled.Duo{4n, 57n, 9, 2},
  TBundled.Duo{5n, 57n, 9, 2}, TBundled.Duo{6n, 57n, 9, 2}, TBundled.Duo{0n, 57n, 9, 2}, TBundled.Duo{13n, 57n, 9, 2},
  TBundled.Duo{14n, 57n, 9, 2}, TBundled.Duo{15n, 57n, 9, 2}, TBundled.Duo{29n, 57n, 9, 2}, TBundled.Duo{30n, 57n, 9, 2},
  TBundled.Duo{31n, 57n, 9, 2}, TBundled.Duo{32n, 57n, 9, 2}, TBundled.Duo{33n, 57n, 9, 2}, TBundled.Duo{34n, 57n, 9, 2},
  TBundled.Duo{35n, 57n, 9, 2}, TBundled.Duo{36n, 57n, 9, 2}, TBundled.Duo{37n, 57n, 9, 2}, TBundled.Duo{38n, 57n, 9, 2},
  TBundled.Duo{39n, 57n, 9, 2}, TBundled.Duo{40n, 57n, 9, 2}, TBundled.Duo{41n, 57n, 9, 2}, TBundled.Duo{44n, 57n, 9, 2},
  TBundled.Duo{11n, 49n, 9, 2}, TBundled.Duo{12n, 50n, 9, 2}, TBundled.Duo{1n, 57n, 3, 1}, TBundled.Duo{2n, 57n, 3, 1},
  TBundled.Duo{3n, 57n, 3, 1}, TBundled.Duo{24n, 57n, 3, 1}, TBundled.Duo{26n, 57n, 3, 1}, TBundled.Duo{27n, 57n, 3, 1},
  TBundled.Duo{42n, 57n, 3, 1}, TBundled.Duo{43n, 57n, 3, 1}, TBundled.Duo{47n, 57n, 3, 1}]

# the pair p meets its contrast in the table xs
def meets(+xs: List<&2, Co.Rgb>, p: TBundled.Duo) -> Bool:
  match p:
    case TBundled.Duo{fg, bg, num, den}:
      Co.contrast_ge(get(xs, fg), get(xs, bg), num, den)

def all_meet(+xs: List<&2, Co.Rgb>, ps: List<&2, TBundled.Duo>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, rest}:
      Bool.and(meets(xs, p), all_meet(xs, rest))

# every pair meets its contrast in the table xs
def legible(+xs: List<&2, Co.Rgb>) -> Bool:
  all_meet(xs, pairs())

def idxs(xs: List<&2, Co.Rgb>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Co.to256(x) <> idxs(rest)

def notin(+x: U32, ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(Bool.not(U32.is_eq(x, y)), notin(x, rest))

# no two values of xs are equal
def distinct(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(notin(x, rest), distinct(rest))

# the status colors accent (0), success (4), warning (6) and error (5) of
# the table xs are pairwise distinct as a 256-color terminal paints them
def status_distinct(+xs: List<&2, Co.Rgb>) -> Bool:
  distinct(idxs([get(xs, 0n), get(xs, 4n), get(xs, 6n), get(xs, 5n)]))
