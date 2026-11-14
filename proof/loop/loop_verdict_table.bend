# eukhe: the proof of LAW loop_verdict_table
#
# PROOF: every row computes: Lp.judge matches the evidence, then the exit
# status (0, 1 + k), and each side is the same verdict; for an exit 1 + k
# the test of 126 and 127 is what the premises rewrite to False.

import Base
import ../../bend/loop.bend as Lp
import ../../laws/loop/model.bend as Loop

# a nonzero exit other than 126 and 127 gives the verdict v
def lvt.other(k: Nat, v: Lp.Verdict, h126: {Nat.is_eq(1n+k, 126n) == False{} : Bool}, h127: {Nat.is_eq(1n+k, 127n) == False{} : Bool}) -> {Lp.judge.nonzero(Lp.cannot_run(1n+k), v) == v : Lp.Verdict}:
  %Equal.sym(Bool, Nat.is_eq(1n+k, 126n), False{}, h126) : {Lp.judge.nonzero(Bool.or(_, Nat.is_eq(1n+k, 127n)), v) == v : Lp.Verdict}
  %Equal.sym(Bool, Nat.is_eq(1n+k, 127n), False{}, h127) : {Lp.judge.nonzero(_, v) == v : Lp.Verdict}
  {==}

def Loop.loop_verdict_table(k, h126, h127):
  +n = k
  +a = h126
  +b = h127
  ({==}, lvt.other(n, Lp.Refuted{}, a, b), {==}, lvt.other(n, Lp.Confirmed{}, a, b), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
