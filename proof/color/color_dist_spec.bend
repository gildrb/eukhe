# eukhe: the proof of LAW color_dist_spec: the same weighted sum, each
# channel distance the spec's (PNear.cn.absd)

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color
import ./color_near_spec.bend as PNear

def Color.color_dist_spec(a, b):
  match a b:
    case Co.Rgb{+ar, +ag, +ab} Co.Rgb{+br, +bg, +bb}:
      +x = Co.absdiff(ar, br)
      +y = Co.absdiff(ag, bg)
      +z = Co.absdiff(ab, bb)
      %PNear.cn.absd(ar, br) : {(299 * (x * x : U32) + 587 * (y * y : U32) + 114 * (z * z : U32) : U32) == (299 * (_ * _ : U32) + 587 * (Color.th.absd(ag, bg) * Color.th.absd(ag, bg) : U32) + 114 * (Color.th.absd(ab, bb) * Color.th.absd(ab, bb) : U32) : U32) : U32}
      %PNear.cn.absd(ag, bg) : {(299 * (x * x : U32) + 587 * (y * y : U32) + 114 * (z * z : U32) : U32) == (299 * (x * x : U32) + 587 * (_ * _ : U32) + 114 * (Color.th.absd(ab, bb) * Color.th.absd(ab, bb) : U32) : U32) : U32}
      %PNear.cn.absd(ab, bb) : {(299 * (x * x : U32) + 587 * (y * y : U32) + 114 * (z * z : U32) : U32) == (299 * (x * x : U32) + 587 * (y * y : U32) + 114 * (_ * _ : U32) : U32) : U32}
      {==}
