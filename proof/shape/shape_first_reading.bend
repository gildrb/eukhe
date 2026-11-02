# eukhe: the proof of LAW shape_first_reading
#
# PROOF: the first mode is the first of the all mode's readings kept by
# the end condition (LF.shf.first), and the all mode reads the spec's
# readings (LAll.shall.all).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ./base.bend as LA
import ./base/first.bend as LF
import ./base/all.bend as LAll

def sfr.head(xs: List<&2, S.St>) -> {S.head(LA.shb.take1(xs)) == Shape.sp_head(xs) : Maybe<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def Shape.shape_first_reading(f, ps, ends, s):
  %Equal.sym(List<&2, S.St>, S.go(f, ps, [s], 0n, S.First{ends}), LA.shb.take1(Shape.sp_keep(ends, S.go(f, ps, [s], 0n, S.All{}))), LF.shf.first(f, ps, [s], 0n, ends)) : {S.head(_) == Shape.sp_head(Shape.sp_keep(ends, Shape.sp_reads(f, ps, [s], 0n))) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, S.go(f, ps, [s], 0n, S.All{}), Shape.sp_reads(f, ps, [s], 0n), LAll.shall.all(f, ps, [s], 0n)) : {S.head(LA.shb.take1(Shape.sp_keep(ends, _))) == Shape.sp_head(Shape.sp_keep(ends, Shape.sp_reads(f, ps, [s], 0n))) : Maybe<&2, S.St>}
  sfr.head(Shape.sp_keep(ends, Shape.sp_reads(f, ps, [s], 0n)))
