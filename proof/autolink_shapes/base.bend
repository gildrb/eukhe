# eukhe: a lemma for the proof of area shape's entry laws
# (proof/shape/base/entry.bend): the autolink table is the spec table
# laws/autolink_shapes.bend sp_table, which laws/shape/entry.bend reads.
# No law states it: sp_table is the table written out again, so it proves
# no requirement of the autolinks (anchored by
# autolink_shapes_link_example, autolink_shapes_backpedal_example and
# autolink_shapes_omp_example).
#
# PROOF: each index computes on both sides; past the last both are none.

import Base
import ../../bend/shape.bend as S
import ../../bend/autolink_shapes.bend as AL
import ../../laws/autolink_shapes.bend as AutolinkShapes

def al.table(i: Nat) -> {AL.shape(i) == List.get(&2, S.Shape, AutolinkShapes.sp_table(), i) : Maybe<&2, S.Shape>}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+k:
      {==}
