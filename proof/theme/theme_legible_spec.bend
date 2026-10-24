# eukhe: the proof of LAW theme_legible_spec: the model's lookup is the
# spec's (lg.at), so each pair meets alike (lg.meets); the model's pair list
# is the spec's, folded alike (lg.go)

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/bundled.bend as TBundled
import ../../spec/theme_rules.bend as Ts
import ../../laws/theme.bend as Theme

def lg.at(xs: List<&2, Co.Rgb>, k: Nat) -> {TPalette.at(xs, k) == Ts.get(xs, k) : Co.Rgb}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      lg.at(t, p)

def lg.meets(+xs: List<&2, Co.Rgb>, p: TBundled.Duo) -> {TBundled.meets(xs, p) == Ts.meets(xs, p) : Bool}:
  match p:
    case TBundled.Duo{+fg, +bg, +num, +den}:
      %lg.at(xs, fg) : {Co.contrast_ge(TPalette.at(xs, fg), TPalette.at(xs, bg), num, den) == Co.contrast_ge(_, Ts.get(xs, bg), num, den) : Bool}
      %lg.at(xs, bg) : {Co.contrast_ge(TPalette.at(xs, fg), TPalette.at(xs, bg), num, den) == Co.contrast_ge(TPalette.at(xs, fg), _, num, den) : Bool}
      {==}

def lg.go(+xs: List<&2, Co.Rgb>, ps: List<&2, TBundled.Duo>) -> {TBundled.legible.go(xs, ps) == Ts.all_meet(xs, ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, rest}:
      %lg.go(xs, rest) : {Bool.and(TBundled.meets(xs, p), TBundled.legible.go(xs, rest)) == Bool.and(Ts.meets(xs, p), _) : Bool}
      %lg.meets(xs, p) : {Bool.and(TBundled.meets(xs, p), TBundled.legible.go(xs, rest)) == Bool.and(_, TBundled.legible.go(xs, rest)) : Bool}
      {==}

def Theme.theme_legible_spec(xs):
  lg.go(xs, TBundled.pairs())
