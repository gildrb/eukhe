# eukhe: the proof of LAW theme_fill_map_spec: induction on the tokens

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../spec/theme/model.bend as Tm
import ../../laws/theme_model.bend as ThemeModel

def ThemeModel.theme_fill_map_spec(cols, bg, ts):
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      %ThemeModel.theme_fill_map_spec(cols, bg, rest) : {TPalette.fill(cols, bg, t) <> TPalette.fill.map(cols, bg, rest) == TPalette.fill(cols, bg, t) <> _ : List<&2, Maybe<&2, TFile.Val>>}
      {==}
