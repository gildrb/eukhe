# eukhe: the proof of LAW tui_effort_shipped_distinct

import Base
import ../../bend/theme.bend as T
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ../base/nat/is_le.bend as LNatIsLe
import ./base.bend as LA

# every shipped ramp is wider than the longest ladder
def pu.shipped_wide(s: T.Shipped) -> {Nat.is_le(TC.ladder.max(), TC.span(TC.shipped.lo(s), TC.shipped.hi(s))) == True{} : Bool}:
  match s:
    case T.Eukhe{}:
      {==}
    case T.Dark{}:
      {==}
    case T.Light{}:
      {==}

def tui_effort_shipped_distinct(+s: T.Shipped, +n: Nat, +fits: {Nat.is_le(n, TC.ladder.max()) == True{} : Bool}) -> {TC.distinct(TC.ramp(TC.shipped.lo(s), TC.shipped.hi(s), n)) == True{} : Bool}:
  +lo = TC.shipped.lo(s)
  +hi = TC.shipped.hi(s)
  LA.tui_effort_ramp_distinct(lo, hi, n, LNatIsLe.pu.le_trans(n, TC.ladder.max(), TC.span(lo, hi), fits, pu.shipped_wide(s)))

def TuiColor.tui_effort_shipped_distinct(s, n, fits):
  tui_effort_shipped_distinct(s, n, fits)
