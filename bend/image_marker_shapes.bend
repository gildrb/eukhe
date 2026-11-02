# image_marker_shapes: the shape of the pasted-image marker the input
# editor reads (eukhe-tui image_markers.rs, TS image-markers.ts; the
# matcher: bend/shape.bend; ids 100-109 of the entry bend/ffi_shape.bend:
# `shape(i)` is the shape of id 100 + i). Above the shape: the
# regex it replaces. `\d` is an ASCII digit here (Rust's is any Unicode
# digit, which the id parse then rejected: an intended difference). Pure:
# no IO, no @unsafe.

import Base
import ./shape.bend as S

# 100 `\[image #(\d+)\]`
def marker() -> S.Shape:
  S.Shape{S.Anywhere{}, [S.Lit{"[image #"}, S.Cap{[S.Run{S.Cls{S.Codes{[S.Rg{48, 57}]}, False{}, False{}}, 1n, None{}}]}, S.Lit{"]"}], False{}}

# The table: the shape of id 100 + i at index i (none past the last); a
# lookup builds only the shape it answers
def shape(i: Nat) -> Maybe<&2, S.Shape>:
  match i:
    case 0n:
      Some{marker()}
    case 1n+k:
      None{}
