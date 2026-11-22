# eukhe: the proof of LAW rec_capped_reads_the_row
#
# PROOF: Rec.capped computes to Rk.capped; a row x is below x + 1 + y and
# x + 2 + y (by induction on x), the lower rung long + 1 below long + 2,
# and the empty rows 0 to 3 below 4.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover

def rcr.ws(a: Nat) -> {RnRecovery.below(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      rcr.ws(b)

def rcr.wb1(x: Nat, -y: Nat) -> {RnRecovery.below(x, 1n+Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+z:
      rcr.wb1(z, y)

def rcr.wb2(x: Nat, -y: Nat) -> {RnRecovery.below(x, 2n+Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+z:
      rcr.wb2(z, y)

def RunRecover.rec_capped_reads_the_row(rc, k, row, same, last, lo, le, rd, rp, x, y):
  ({==}, ({==}, (rcr.wb2(x, y), (rcr.ws(lo), (rcr.wb1(x, y), (rcr.wb1(x, y), ({==}, ({==}, ({==}, {==})))))))))
