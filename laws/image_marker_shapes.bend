# eukhe: the laws of area image_marker_shapes

import Base
import ../bend/shape.bend as S
import ../bend/image_marker_shapes.bend as IM

# (IM1) The shape of the pasted-image marker
# ------------------------------------------
# bend/image_marker_shapes.bend, ids 100-109 of the entry
# bend/ffi_shape.bend (eukhe-tui image_markers.rs asks it through
# eukhe-tui text_shapes.rs, in place of its regex). The matcher is pinned
# by laws/shape/match.bend and laws/shape/search.bend. "the text holds" a
# shape read at the leftmost place it fits; "a number" one or more ASCII
# digits 0-9 (Rust's `\d` takes every Unicode digit, which the id parse
# then rejects: an intended difference).
#
# R1: id 100, a marker: the text holds `[image #`, a number (captured: the
#     id), `]`.
# R2: the table holds exactly this shape, at index 0, and no other.

# Spec helpers
# ------------

# R1
def sp_marker() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"[image #"}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{"]"}], False{}}

# Laws
# ----

# LAW image_marker_shapes_table (R1, R2): at index 0 the table holds the
# shape R1 states, and none past it
# EXCLUDES: a marker shape that drifts from the regex it replaced (another
#   literal, a digit class past 0-9, a missing capture), an id shifted, a
#   lookup that answers a shape past the last
law image_marker_shapes_table:
  for +i: Nat
  {IM.shape(i) == List.get(&2, S.Shape, [sp_marker()], i) : Maybe<&2, S.Shape>}

# LAW image_marker_shapes_example (R1): anchor: the marker test's text gives
# its three ids in order, a repeated one too; ids that are no number are
# no markers
# EXCLUDES: a table that drifts from the marker tests
# waive L4-examples-only: a shape is a constant, no input to leave free;
#   image_marker_shapes_table pins it whole to its R rule
law image_marker_shapes_example:
  {[S.all(IM.marker(), "a [image #1] b [image #2] [image #1]"), S.all(IM.marker(), "[image #x] [image #1.5]")] == [[S.Fit{2n, 12n, [Some{"1"}]}, S.Fit{15n, 25n, [Some{"2"}]}, S.Fit{26n, 36n, [Some{"1"}]}], []] : List<&2, List<&2, S.Fit>>}
