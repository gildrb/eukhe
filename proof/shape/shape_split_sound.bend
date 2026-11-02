# eukhe: the proof of LAW shape_split_sound
#
# PROOF: LS.shs.sound, by induction along the spec's readings, with the
# fuel one past the chars after the place.

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ./base/sound.bend as LS

def Shape.shape_split_sound(ps, s, r, h):
  LS.shs.sound(1n+Shape.sp_left(s), ps, s, 0n, r, LS.shs.lt_self(Shape.sp_left(s)), h)
