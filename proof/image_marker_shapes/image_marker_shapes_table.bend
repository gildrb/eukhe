# eukhe: the proof of LAW image_marker_shapes_table
#
# PROOF: each index computes on both sides; past the last both are none.

import Base
import ../../bend/shape.bend as S
import ../../bend/image_marker_shapes.bend as IM
import ../../laws/image_marker_shapes.bend as ImageMarkerShapes

def ImageMarkerShapes.image_marker_shapes_table(i):
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}
