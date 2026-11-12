# eukhe: a lemma for the proof of area shape's entry laws
# (proof/shape/base/entry.bend): the preview table is the spec table
# laws/preview_shapes.bend sp_table, which laws/shape/entry.bend reads. No
# law states it: sp_table is the table written out again, so it proves no
# requirement of the preview shapes (those are anchored by the
# preview_shapes_*_example laws).
#
# PROOF: each index computes on both sides; past the last both are none.

import Base
import ../../bend/shape.bend as S
import ../../bend/preview_shapes.bend as PS
import ../../laws/preview_shapes.bend as PreviewShapes

def pv.table(i: Nat) -> {PS.shape(i) == List.get(&2, S.Shape, PreviewShapes.sp_table(), i) : Maybe<&2, S.Shape>}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n:
      {==}
    case 45n:
      {==}
    case 46n:
      {==}
    case 47n+k:
      {==}
