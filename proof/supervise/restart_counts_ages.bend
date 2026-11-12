# eukhe: the proof of LAW restart_counts_ages
# The decided state is the new failure in front of the kept ages, counted
# as one more than the ages kept.

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise

def Supervise.restart_counts_ages(c, s, g):
  match s:
    case Su.St{a, n}:
      {==}
