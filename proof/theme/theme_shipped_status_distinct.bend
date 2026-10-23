# eukhe: the proof of LAW theme_shipped_status_distinct

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws

def theme_shipped_status_distinct(s: T.Shipped) -> {T.status_distinct(T.table(s)) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}

def Laws.theme_shipped_status_distinct(s):
  theme_shipped_status_distinct(s)
