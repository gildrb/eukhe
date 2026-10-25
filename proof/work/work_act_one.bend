# eukhe: the proof of LAW work_act_one
# An act's number is a tower: its height says whether it has a call and
# which, its bottom is its result (LAWork.wt.tower); the laws' Maybe
# equality is the model's on every case.

import Base
import ../../laws/work.bend as Work
import ./base.bend as LWork

def Work.work_act_one(a, b, x, y):
  match a b:
    case None{} None{}:
      LWork.wt.tower(1n, 1n, x, y)
    case None{} Some{d}:
      LWork.wt.tower(1n, 2n+d, x, y)
    case Some{c} None{}:
      LWork.wt.tower(2n+c, 1n, x, y)
    case Some{c} Some{d}:
      LWork.wt.tower(2n+c, 2n+d, x, y)
