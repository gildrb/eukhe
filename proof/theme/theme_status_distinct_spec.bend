# eukhe: the proof of LAW theme_status_distinct_spec: the four status
# colors are the spec's lookups (PLeg.lg.at), quantized alike (sd.idxs),
# then tested alike for distinctness (sd.distinct)

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/bundled.bend as TBundled
import ../../spec/theme_rules.bend as Ts
import ../../laws/theme.bend as Theme
import ./theme_legible_spec.bend as PLeg

def sd.idxs(xs: List<&2, Co.Rgb>) -> {TBundled.to256s(xs) == Ts.idxs(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      %sd.idxs(rest) : {Co.to256(x) <> TBundled.to256s(rest) == Co.to256(x) <> _ : List<&2, U32>}
      {==}

def sd.notin(+x: U32, ys: List<&2, U32>) -> {TBundled.notin(x, ys) == Ts.notin(x, ys) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{y, rest}:
      %sd.notin(x, rest) : {Bool.and(U32.is_ne(x, y), TBundled.notin(x, rest)) == Bool.and(U32.is_ne(x, y), _) : Bool}
      {==}

def sd.distinct(xs: List<&2, U32>) -> {TBundled.distinct(xs) == Ts.distinct(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %sd.distinct(rest) : {Bool.and(TBundled.notin(x, rest), TBundled.distinct(rest)) == Bool.and(Ts.notin(x, rest), _) : Bool}
      %sd.notin(x, rest) : {Bool.and(TBundled.notin(x, rest), TBundled.distinct(rest)) == Bool.and(_, TBundled.distinct(rest)) : Bool}
      {==}

def Theme.theme_status_distinct_spec(xs):
  +l = TBundled.distinct(TBundled.to256s([TPalette.at(xs, 0n), TPalette.at(xs, 4n), TPalette.at(xs, 6n), TPalette.at(xs, 5n)]))
  %PLeg.lg.at(xs, 0n) : {l == Ts.distinct(Ts.idxs([_, Ts.get(xs, 4n), Ts.get(xs, 6n), Ts.get(xs, 5n)])) : Bool}
  %PLeg.lg.at(xs, 4n) : {l == Ts.distinct(Ts.idxs([TPalette.at(xs, 0n), _, Ts.get(xs, 6n), Ts.get(xs, 5n)])) : Bool}
  %PLeg.lg.at(xs, 6n) : {l == Ts.distinct(Ts.idxs([TPalette.at(xs, 0n), TPalette.at(xs, 4n), _, Ts.get(xs, 5n)])) : Bool}
  %PLeg.lg.at(xs, 5n) : {l == Ts.distinct(Ts.idxs([TPalette.at(xs, 0n), TPalette.at(xs, 4n), TPalette.at(xs, 6n), _])) : Bool}
  +ys = {[TPalette.at(xs, 0n), TPalette.at(xs, 4n), TPalette.at(xs, 6n), TPalette.at(xs, 5n)] : List<&2, Co.Rgb>}
  %sd.idxs(ys) : {l == Ts.distinct(_) : Bool}
  sd.distinct(TBundled.to256s(ys))
