# eukhe: the proof of LAW shape_fuel_enough
#
# PROOF: S.go reads the spec's readings for every fuel (LAll.shall.all), and
# those do not depend on a fuel past the place's count of chars after it
# (LU.shu.fi, between the fuel and one past that count).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ../../laws/shape/search.bend as ShapeSearch
import ./base/fuel.bend as LU
import ./base/sound.bend as LS
import ./base/all.bend as LAll

def ShapeSearch.shape_fuel_enough(f, ps, s, h):
  +F = {1n+Shape.sp_left(s) : Nat}
  +fi = LU.shu.fi(f, F, ps, [s], 0n, LU.shu.one(f, s, h), LU.shu.one(F, s, LS.shs.lt_self(Shape.sp_left(s))))
  Equal.trans(List<&2, S.St>, S.go(f, ps, [s], 0n), Shape.sp_reads(f, ps, [s], 0n), S.go(F, ps, [s], 0n), LAll.shall.all(f, ps, [s], 0n), Equal.trans(List<&2, S.St>, Shape.sp_reads(f, ps, [s], 0n), Shape.sp_reads(F, ps, [s], 0n), S.go(F, ps, [s], 0n), fi, Equal.sym(List<&2, S.St>, S.go(F, ps, [s], 0n), Shape.sp_reads(F, ps, [s], 0n), LAll.shall.all(F, ps, [s], 0n))))
