# eukhe: the proof of LAW autolink_shapes_table
#
# PROOF: each index computes on both sides; past the last both are none.

import Base
import ../../bend/shape.bend as S
import ../../bend/autolink_shapes.bend as AL
import ../../laws/autolink_shapes.bend as AutolinkShapes

def AutolinkShapes.autolink_shapes_table(i):
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+k:
      {==}
