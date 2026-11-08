# eukhe: the proof of LAW color_contrast_wcag_example: the test past terms
# of 40 (21.00001) is its decision on bits (LCd.cd.wide, from LAW
# color_contrast_exact_wide), which the checker computes; the others compute

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./color_contrast_exact_wide/decide.bend as LCd

def Color.color_contrast_wcag_example():
  %LCd.cd.wide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 2100001, 100000, {==}) : {[Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 21, 1), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, 21, 1), _, Co.contrast_ge(Co.Rgb{118, 118, 118}, Co.Rgb{255, 255, 255}, 9, 2), Co.contrast_ge(Co.Rgb{119, 119, 119}, Co.Rgb{255, 255, 255}, 9, 2)] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
  {==}
