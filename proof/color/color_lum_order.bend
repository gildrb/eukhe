# eukhe: the proof of LAW color_lum_order: blue alone at most red alone at
# most green alone, at every leaf of lin's table (one closed check), so at
# lin(c) for every c (cl.lin, a walk of the table)

import Base
import ../../laws/color/math.bend as Color
import ./base/lum.bend as LCl

def Color.color_lum_order(c):
  LCl.cl.lin(LCl.ClOrder{}, c, {==}, {==})
