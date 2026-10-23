# eukhe: the proof of LAW tui_roles_shipped

import Base
import ../../bend/theme/bundled.bend as TBundled
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

def tui_roles_shipped(s: TBundled.Shipped) -> {TC.paints(TBundled.table(s), TC.roles()) == True{} : Bool}:
  match s:
    case TBundled.Eukhe{}:
      {==}
    case TBundled.Dark{}:
      {==}
    case TBundled.Light{}:
      {==}

def TuiColor.tui_roles_shipped(s):
  tui_roles_shipped(s)
