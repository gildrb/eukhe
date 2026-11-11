# eukhe: a lemma for the proof of area shape's entry laws
# (proof/shape/base/entry.bend): the marker table is the spec helper
# laws/image_marker_shapes.bend sp_marker at index 0, none past it, which
# laws/shape/entry.bend reads. No law states it: sp_marker is the shape
# written out again, so it proves no requirement of the marker (anchored
# by image_marker_shapes_example).
#
# PROOF: each index computes on both sides; past the last both are none.

import Base
import ../../bend/shape.bend as S
import ../../bend/image_marker_shapes.bend as IM
import ../../laws/image_marker_shapes.bend as ImageMarkerShapes

def im.table(i: Nat) -> {IM.shape(i) == List.get(&2, S.Shape, [ImageMarkerShapes.sp_marker()], i) : Maybe<&2, S.Shape>}:
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}
