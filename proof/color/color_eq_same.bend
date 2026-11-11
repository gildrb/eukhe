# eukhe: the proof of LAW color_eq_same: each channel equals itself (a walk
# of its bits, LCw.cw.refl)

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/word.bend as LCw

def Color.color_eq_same(a):
  match a:
    case Co.Rgb{+r, +g, +b}:
      %Equal.sym(Bool, U32.is_eq(r, r), True{}, LCw.cw.refl(r)) : {Bool.and(_, Bool.and(U32.is_eq(g, g), U32.is_eq(b, b))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(g, g), True{}, LCw.cw.refl(g)) : {Bool.and(_, U32.is_eq(b, b)) == True{} : Bool}
      LCw.cw.refl(b)
