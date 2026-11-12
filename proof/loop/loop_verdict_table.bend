# eukhe: the proof of LAW loop_verdict_table
#
# PROOF: every row computes: Lp.judge matches the evidence, then the exit
# status (0, 1, 2 + k), and each side is the same verdict.

import Base
import ../../laws/loop/model.bend as Loop

def Loop.loop_verdict_table(k):
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
