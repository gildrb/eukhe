# eukhe: the proof of LAW theme_concrete_of_base: one case per value

import Base
import ../../laws/theme_model.bend as ThemeModel

def ThemeModel.theme_concrete_of_base(m):
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}
