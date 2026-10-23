# eukhe: the proof of LAW theme_shipped_legible

import Base
import ../../bend/theme/bundled.bend as TBundled
import ../../laws/theme.bend as Theme

# Shipped themes
# --------------

def theme_shipped_legible(s: TBundled.Shipped) -> {TBundled.legible(TBundled.table(s)) == True{} : Bool}:
  match s:
    case TBundled.Eukhe{}:
      {==}
    case TBundled.Dark{}:
      {==}
    case TBundled.Light{}:
      {==}

def Theme.theme_shipped_legible(s):
  theme_shipped_legible(s)
