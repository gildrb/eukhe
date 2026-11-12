# eukhe: the proof of LAW color_eq_sound: the three channel tests hold, and
# two U32 that compare equal are one value (LCl.cl.eq)

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/lum.bend as LCl
import ./base/word.bend as LCw

def ceq.go(+ar: U32, +ag: U32, +ab: U32, +br: U32, +bg: U32, +bb: U32, +same: {Bool.and(U32.is_eq(ar, br), Bool.and(U32.is_eq(ag, bg), U32.is_eq(ab, bb))) == True{} : Bool}) -> {Co.Rgb{ar, ag, ab} == Co.Rgb{br, bg, bb} : Co.Rgb}:
  +hr = LCw.cw.and_l(U32.is_eq(ar, br), Bool.and(U32.is_eq(ag, bg), U32.is_eq(ab, bb)), same)
  +hgb = LCw.cw.and_r(U32.is_eq(ar, br), Bool.and(U32.is_eq(ag, bg), U32.is_eq(ab, bb)), same)
  +hg = LCw.cw.and_l(U32.is_eq(ag, bg), U32.is_eq(ab, bb), hgb)
  +hb = LCw.cw.and_r(U32.is_eq(ag, bg), U32.is_eq(ab, bb), hgb)
  %LCl.cl.eq(ar, br, hr) : {Co.Rgb{ar, ag, ab} == Co.Rgb{_, bg, bb} : Co.Rgb}
  %LCl.cl.eq(ag, bg, hg) : {Co.Rgb{ar, ag, ab} == Co.Rgb{ar, _, bb} : Co.Rgb}
  %LCl.cl.eq(ab, bb, hb) : {Co.Rgb{ar, ag, ab} == Co.Rgb{ar, ag, _} : Co.Rgb}
  {==}

def Color.color_eq_sound(a, b, same):
  match a b:
    case Co.Rgb{ar, ag, ab} Co.Rgb{br, bg, bb}:
      ceq.go(ar, ag, ab, br, bg, bb, same)
