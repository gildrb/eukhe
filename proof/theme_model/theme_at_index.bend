# eukhe: the proof of LAW theme_at_index: induction on the colors before

import Base
import ../../laws/theme_model.bend as ThemeModel

def ThemeModel.theme_at_index(pre, c, post):
  match pre:
    case Nil{}:
      {==}
    case Con{x, rest}:
      ThemeModel.theme_at_index(rest, c, post)
