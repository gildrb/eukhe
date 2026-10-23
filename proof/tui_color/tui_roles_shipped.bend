# eukhe: the proof of LAW tui_roles_shipped

import Base
import ../../bend/theme.bend as T
import ../../bend/tui_color.bend as TC
import ../../LAWS.bend as Laws

def tui_roles_shipped(s: T.Shipped) -> {TC.paints(T.table(s), TC.roles()) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}

def Laws.tui_roles_shipped(s):
  tui_roles_shipped(s)
