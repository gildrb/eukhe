# eukhe: the proof of LAW theme_shipped_status_distinct

import Base
import ../../bend/theme/bundled.bend as TBundled
import ../../laws/theme.bend as Theme

def theme_shipped_status_distinct(s: TBundled.Shipped) -> {TBundled.status_distinct(TBundled.table(s)) == True{} : Bool}:
  match s:
    case TBundled.Eukhe{}:
      {==}
    case TBundled.Dark{}:
      {==}
    case TBundled.Light{}:
      {==}

def Theme.theme_shipped_status_distinct(s):
  theme_shipped_status_distinct(s)
