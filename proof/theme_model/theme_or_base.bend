# eukhe: the proof of LAW theme_or_base: one case per first value

import Base
import ../../laws/theme_model.bend as ThemeModel

def ThemeModel.theme_or_base(A, a, b, d):
  match a:
    case None{}:
      ({==}, {==})
    case Some{x}:
      ({==}, {==})
