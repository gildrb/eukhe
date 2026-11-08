# eukhe: the proof of LAW color_lum_grey: the three weighted terms of a gray
# sum to 10000 times its linear value at every leaf of lin's table (one
# closed check), so at lin(c) for every c (cl.lin, a walk of the table)

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/lum.bend as LCl

def Color.color_lum_grey(c):
  LCl.cl.eq((2126 * Co.lin(c) + 7152 * Co.lin(c) + 722 * Co.lin(c) : U32), (10000 * Co.lin(c) : U32), LCl.cl.lin(LCl.ClGrey{}, c, {==}, {==}))
