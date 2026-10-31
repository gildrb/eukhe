# eukhe: the proof of LAW theme_vals_spec: induction on the palette

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../spec/theme/model.bend as Tm
import ../../laws/theme_model.bend as ThemeModel

def ThemeModel.theme_vals_spec(p):
  match p:
    case Nil{}:
      {==}
    case Con{m, +rest}:
      match m:
        case None{}:
          %ThemeModel.theme_vals_spec(rest) : {TFile.Dflt{} <> TPalette.vals(rest) == TFile.Dflt{} <> _ : List<&2, TFile.Val>}
          {==}
        case Some{v}:
          %ThemeModel.theme_vals_spec(rest) : {v <> TPalette.vals(rest) == v <> _ : List<&2, TFile.Val>}
          {==}
