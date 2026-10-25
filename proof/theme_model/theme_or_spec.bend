# eukhe: the proof of LAW theme_or_spec: one case per first value

import Base
import ../../laws/theme_model.bend as ThemeModel

def ThemeModel.theme_or_spec(A, a, b, d):
  match a:
    case None{}:
      ({==}, {==})
    case Some{x}:
      ({==}, {==})
