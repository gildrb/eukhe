# eukhe: the proof of LAW theme_palette_name_free

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws

def theme_palette_name_free(f: T.Th, n: String) -> {T.palette(T.rename(f, n)) == T.palette(f) : List<&2, Maybe<&2, T.Val>>}:
  match f:
    case T.Th{name, cols, page, card, info}:
      {==}

def Laws.theme_palette_name_free(f, n):
  theme_palette_name_free(f, n)
