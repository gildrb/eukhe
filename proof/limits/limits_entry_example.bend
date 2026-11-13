# eukhe: the proof of LAW limits_entry_example
#
# PROOF: each request computes.

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB

def Limits.limits_entry_example():
  ({==}, {==})
