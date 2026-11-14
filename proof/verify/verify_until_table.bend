# eukhe: the proof of LAW verify_until_table
#
# PROOF: the eight rows; an exit 1+p computes to the test of 126 and 127,
# which the premises rewrite to False: refuted; every other row computes.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def vut.other(p: Nat, h126: {Nat.is_eq(1n+p, 126n) == False{} : Bool}, h127: {Nat.is_eq(1n+p, 127n) == False{} : Bool}) -> {V.grade_until(V.Exited{1n+p}) == V.Refuted{} : V.Verdict}:
  %Equal.sym(Bool, Nat.is_eq(1n+p, 126n), False{}, h126) : {V.grade_until.nonzero(Bool.or(_, Nat.is_eq(1n+p, 127n))) == V.Refuted{} : V.Verdict}
  %Equal.sym(Bool, Nat.is_eq(1n+p, 127n), False{}, h127) : {V.grade_until.nonzero(_) == V.Refuted{} : V.Verdict}
  {==}

def Verify.verify_until_table(p, h126, h127):
  ({==}, (vut.other(p, h126, h127), ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))
