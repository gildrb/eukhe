# eukhe: the proof of LAW shape_split_complete
#
# PROOF: LC.shc.complete, by induction along the split, with the fuel one
# past the chars after the place.

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ./base/sound.bend as LS
import ./base/complete.bend as LC

def Shape.shape_split_complete(ps, ws, s, r, h):
  LC.shc.complete(ws, ps, 0n, s, r, 1n+Shape.sp_left(s), LS.shs.lt_self(Shape.sp_left(s)), h)
