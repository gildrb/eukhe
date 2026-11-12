# eukhe: the proof of LAW color_light_rises: light is the luminance above
# one half, and a luminance at least one that is above one half is above
# it (the order of three words, LCw.cw.le_gt)

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/word.bend as LCw

def Color.color_light_rises(a, b, le, la):
  LCw.cw.le_gt(Co.lum(a), Co.lum(b), 50000000, le, la)
