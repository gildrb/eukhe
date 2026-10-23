# eukhe: the proof of LAW theme_shipped_legible

import Base
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme

# Shipped themes
# --------------

def theme_shipped_legible(s: T.Shipped) -> {T.legible(T.table(s)) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}

def Theme.theme_shipped_legible(s):
  theme_shipped_legible(s)
