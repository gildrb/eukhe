# eukhe: the proof of LAW color_contrast_carry_example: each test is its
# decision on bits (LCd.cd.wide, from LAW color_contrast_exact_wide),
# which the checker computes

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./color_contrast_exact_wide/decide.bend as LCd

def Color.color_contrast_carry_example():
  %LCd.cd.wide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65537, {==}) : {[_, Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65536), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65537, 65536), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376256, 65536), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376257, 65536)] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65536, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65537), _, Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65537, 65536), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376256, 65536), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376257, 65536)] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65537, 65536, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65537), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65536), _, Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376256, 65536), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376257, 65536)] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376256, 65536, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65537), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65536), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65537, 65536), _, Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376257, 65536)] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
  %LCd.cd.wide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376257, 65536, {==}) : {[LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65537), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65536), LCd.cd.decide(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65537, 65536), LCd.cd.decide(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376256, 65536), _] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}
  {==}
