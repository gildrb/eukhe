# eukhe: the proof of LAW theme_mode_name_free

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme

def theme_mode_name_free(f: T.Th, n: String) -> {T.light(T.rename(f, n)) == T.light(f) : Bool}:
  match f:
    case T.Th{name, cols, page, card, info}:
      {==}

def Theme.theme_mode_name_free(f, n):
  theme_mode_name_free(f, n)
