# eukhe: a lemma for the proof of area shape's entry laws
# (proof/shape/base/entry.bend): the argument token table is the spec table
# laws/arg_token_shapes.bend sp_table, which laws/shape/entry.bend reads.
# No law states it: sp_table is the table written out again, so it proves
# no requirement of the argument tokens (anchored by
# arg_token_shapes_example).
#
# PROOF: each index computes on both sides; past the last both are none.

import Base
import ../../bend/shape.bend as S
import ../../bend/arg_token_shapes.bend as AT
import ../../laws/arg_token_shapes.bend as ArgTokenShapes

def at.table(i: Nat) -> {AT.shape(i) == List.get(&2, S.Shape, ArgTokenShapes.sp_table(), i) : Maybe<&2, S.Shape>}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+k:
      {==}
