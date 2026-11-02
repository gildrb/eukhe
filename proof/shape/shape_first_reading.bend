# eukhe: the proof of LAW shape_first_reading
#
# PROOF: `at` is the first reading of S.go whose end condition holds
# (LF.shfe.first_end), and S.go reads the spec's readings (LAll.shall.all).

import Base
import ../../bend/shape.bend as S
import ../../laws/shape/match.bend as Shape
import ./base/first.bend as LF
import ./base/all.bend as LAll

def Shape.shape_first_reading(f, ps, ends, s):
  %Equal.sym(Maybe<&2, S.St>, S.first_end(ends, S.go(f, ps, [s], 0n)), Shape.sp_head(Shape.sp_keep(ends, S.go(f, ps, [s], 0n))), LF.shfe.first_end(ends, S.go(f, ps, [s], 0n))) : {_ == Shape.sp_answer(f, ps, ends, s) : Maybe<&2, S.St>}
  %Equal.sym(List<&2, S.St>, S.go(f, ps, [s], 0n), Shape.sp_reads(f, ps, [s], 0n), LAll.shall.all(f, ps, [s], 0n)) : {Shape.sp_head(Shape.sp_keep(ends, _)) == Shape.sp_answer(f, ps, ends, s) : Maybe<&2, S.St>}
  {==}
