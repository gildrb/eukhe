# eukhe: the proof of LAW color_contrast_no_wrap_example: each test past
# terms of 40 is its decision on bits (LCd.cd.wide, from LAW
# color_contrast_exact_wide), which the checker computes; the checker
# counts a Nat one successor at a time, so the products cannot be
# computed as naturals

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./color_contrast_exact_wide/decide.bend as LCd

def Color.color_contrast_no_wrap_example():
  %LCd.cd.wide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 45, 10, {==}) : {[_, Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 40, 40), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000000, 200000000), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000001, 200000000)] == [False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 41, 40, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 45, 10), _, Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 40, 40), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000000, 200000000), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000001, 200000000)] == [False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 41, 40, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 45, 10), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 40, 40), _, Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000000, 200000000), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000001, 200000000)] == [False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000000, 200000000, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 45, 10), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 40, 40), LCd.cd.decide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 41, 40), _, Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000001, 200000000)] == [False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000001, 200000000, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 45, 10), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 40, 40), LCd.cd.decide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 41, 40), LCd.cd.decide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000000, 200000000), _] == [False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}
  {==}
