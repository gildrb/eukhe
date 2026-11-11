# theme_rules (spec): token k of a color table, as the laws of area theme
# read the shipped tables (laws/theme.bend: theme_legible_sound,
# th.apart), and the color a value paints (spec/theme/model.bend). A
# spec: the shipped code never calls it.

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile

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
