# eukhe: the proof of LAW theme_vals_each: induction on the first run

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme_model.bend as ThemeModel

def tve.app(xs: List<&2, Maybe<&2, TFile.Val>>, +ys: List<&2, Maybe<&2, TFile.Val>>) -> {TPalette.vals(List.append(&2, Maybe<&2, TFile.Val>, xs, ys)) == List.append(&2, TFile.Val, TPalette.vals(xs), TPalette.vals(ys)) : List<&2, TFile.Val>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, rest}:
      %tve.app(rest, ys) : {TPalette.or_else(TFile.Val, m, TFile.Dflt{}) <> TPalette.vals(List.append(&2, Maybe<&2, TFile.Val>, rest, ys)) == TPalette.or_else(TFile.Val, m, TFile.Dflt{}) <> _ : List<&2, TFile.Val>}
      {==}

def ThemeModel.theme_vals_each(xs, ys, v):
  (tve.app(xs, ys), {==})
