# eukhe: the proof of LAW arg_token_shapes_table
#
# PROOF: each index computes on both sides; past the last both are none.

import Base
import ../../bend/shape.bend as S
import ../../bend/arg_token_shapes.bend as AT
import ../../laws/arg_token_shapes.bend as ArgTokenShapes

def ArgTokenShapes.arg_token_shapes_table(i):
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+k:
      {==}
