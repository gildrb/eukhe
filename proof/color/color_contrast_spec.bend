# eukhe: the proof of LAW color_contrast_spec: the luminances are the
# spec's (cc.lum); with terms up to 40 the test takes the direct U32
# path; whichever luminance is lower, min and max pick the same darker and
# lighter as the spec (cc.b, a case split on the comparison)

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color

def cc.lum(c: Co.Rgb) -> {Co.lum(c) == Color.th.lum(c) : U32}:
  match c:
    case Co.Rgb{r, g, b}:
      {==}

def cc.b(t: Bool, +x: U32, +y: U32, +num: U32, +den: U32) -> {U32.is_le(((Bool.pick(U32, t, x, y) + Co.flare() : U32) * num : U32), ((Bool.pick(U32, t, y, x) + Co.flare() : U32) * den : U32)) == Color.th.ratio.if(t, x, y, num, den) : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

def cc.go(la: U32, lb: U32, +num: U32, +den: U32) -> {U32.is_le(((U32.min(la, lb) + Co.flare() : U32) * num : U32), ((U32.max(la, lb) + Co.flare() : U32) * den : U32)) == Color.th.ratio.if(U32.is_lt(la, lb), la, lb, num, den) : Bool}:
  match la lb:
    case U32{+x} U32{+y}:
      cc.b(U32.is_lt(U32{x}, U32{y}), U32{x}, U32{y}, num, den)

def Color.color_contrast_spec(a, b, num, den, small):
  %cc.lum(a) : {Co.contrast_ge(a, b, num, den) == Color.th.ratio.if(U32.is_lt(_, Color.th.lum(b)), _, Color.th.lum(b), num, den) : Bool}
  %cc.lum(b) : {Co.contrast_ge(a, b, num, den) == Color.th.ratio.if(U32.is_lt(Co.lum(a), _), Co.lum(a), _, num, den) : Bool}
  %Equal.sym(Bool, Bool.and(U32.is_le(num, 40), U32.is_le(den, 40)), True{}, small) : {Co.contrast.pick(_, (U32.min(Co.lum(a), Co.lum(b)) + Co.flare() : U32), (U32.max(Co.lum(a), Co.lum(b)) + Co.flare() : U32), num, den) == Color.th.ratio.if(U32.is_lt(Co.lum(a), Co.lum(b)), Co.lum(a), Co.lum(b), num, den) : Bool}
  cc.go(Co.lum(a), Co.lum(b), num, den)
