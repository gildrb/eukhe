# eukhe: the proof of LAW cow_same_exact
# The model's equality is the spec's, case by case.

import Base
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LACow

def Sandbox.cow_same_exact(a, b):
  LACow.cw.same(a, b)
