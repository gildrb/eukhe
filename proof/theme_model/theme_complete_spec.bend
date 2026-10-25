# eukhe: the proof of LAW theme_complete_spec: induction on the palette

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../spec/theme_model.bend as Tm
import ../../laws/theme_model.bend as ThemeModel

def ThemeModel.theme_complete_spec(p):
  match p:
    case Nil{}:
      {==}
    case Con{m, rest}:
      match m:
        case None{}:
          {==}
        case Some{v}:
          ThemeModel.theme_complete_spec(rest)
