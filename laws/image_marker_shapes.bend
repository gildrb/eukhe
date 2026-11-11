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
#
# R1 and R2 are anchored only (image_marker_shapes_example): no source
# outside eukhe's code states the shape (no requirement holds an
# image-marker regex), so a law over the table would compare it with
# itself; a law by meaning over every text needs the matcher's search
# (bend/shape.bend seek) reasoned through for this shape, not done.

# Spec helpers
# ------------

# the marker shape written out, read by laws/shape/entry.bend
# (sp_shape_of, area shape) for ids 100-109; no law of this area uses it
def sp_marker() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"[image #"}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{"]"}], False{}}

# Laws
# ----

# LAW image_marker_shapes_example (R1): anchor: the marker test's text
# (crates/eukhe-tui/src/image_markers.rs tests) gives its three ids in
# order, a repeated one too; ids that are no number, an empty number, a
# number not closed by `]` and a marker in another case are no markers
# EXCLUDES: a marker shape that drifts from the marker tests (another
#   literal, a digit class past 0-9, a missing capture, an empty number)
law image_marker_shapes_example:
  {[S.all(IM.marker(), "a [image #1] b [image #2] [image #1]"), S.all(IM.marker(), "[image #x] [image #1.5]"), S.all(IM.marker(), "[image #] [image #12 [Image #3]"), S.all(IM.marker(), "[[image #07]]")] == [[S.Fit{2n, 12n, [Some{"1"}]}, S.Fit{15n, 25n, [Some{"2"}]}, S.Fit{26n, 36n, [Some{"1"}]}], [], [], [S.Fit{1n, 12n, [Some{"07"}]}]] : List<&2, List<&2, S.Fit>>}
