# eukhe: the proof of LAW theme_hex_value

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color

def Color.theme_hex_value(a1, a2, a3, a4, a5, a6, x1, x2, x3, x4, x5, x6, h1, h2, h3, h4, h5, h6):
  +want = {Some{Co.Rgb{(x1 * 16 + x2 : U32), (x3 * 16 + x4 : U32), (x5 * 16 + x6 : U32)}} : Maybe<&2, Co.Rgb>}
  %Equal.sym(Maybe<&2, U32>, Co.hexd(a1), Some{x1}, h1) : {Co.hex.sharp(True{}, Co.hex.rgb(Co.join(16, _, Co.hexd(a2)), Co.join(16, Co.hexd(a3), Co.hexd(a4)), Co.join(16, Co.hexd(a5), Co.hexd(a6)))) == want : Maybe<&2, Co.Rgb>}
  %Equal.sym(Maybe<&2, U32>, Co.hexd(a2), Some{x2}, h2) : {Co.hex.sharp(True{}, Co.hex.rgb(Co.join(16, Some{x1}, _), Co.join(16, Co.hexd(a3), Co.hexd(a4)), Co.join(16, Co.hexd(a5), Co.hexd(a6)))) == want : Maybe<&2, Co.Rgb>}
  %Equal.sym(Maybe<&2, U32>, Co.hexd(a3), Some{x3}, h3) : {Co.hex.sharp(True{}, Co.hex.rgb(Co.join(16, Some{x1}, Some{x2}), Co.join(16, _, Co.hexd(a4)), Co.join(16, Co.hexd(a5), Co.hexd(a6)))) == want : Maybe<&2, Co.Rgb>}
  %Equal.sym(Maybe<&2, U32>, Co.hexd(a4), Some{x4}, h4) : {Co.hex.sharp(True{}, Co.hex.rgb(Co.join(16, Some{x1}, Some{x2}), Co.join(16, Some{x3}, _), Co.join(16, Co.hexd(a5), Co.hexd(a6)))) == want : Maybe<&2, Co.Rgb>}
  %Equal.sym(Maybe<&2, U32>, Co.hexd(a5), Some{x5}, h5) : {Co.hex.sharp(True{}, Co.hex.rgb(Co.join(16, Some{x1}, Some{x2}), Co.join(16, Some{x3}, Some{x4}), Co.join(16, _, Co.hexd(a6)))) == want : Maybe<&2, Co.Rgb>}
  %Equal.sym(Maybe<&2, U32>, Co.hexd(a6), Some{x6}, h6) : {Co.hex.sharp(True{}, Co.hex.rgb(Co.join(16, Some{x1}, Some{x2}), Co.join(16, Some{x3}, Some{x4}), Co.join(16, Some{x5}, _))) == want : Maybe<&2, Co.Rgb>}
  {==}
