# eukhe: the proof of LAW shape_fuel_enough
#
# PROOF: fuel independence (LU.shu.fi) between the fuel and one past the
# place's count of chars after it.

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/fuel.bend as LU
import ./base/sound.bend as LS

def ShapeSearch.shape_fuel_enough(f, ps, s, h):
  LU.shu.fi(f, 1n+Shape.sp_left(s), ps, [s], 0n, LU.shu.one(f, s, h), LU.shu.one(1n+Shape.sp_left(s), s, LS.shs.lt_self(Shape.sp_left(s))))
