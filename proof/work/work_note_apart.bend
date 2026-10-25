# eukhe: the proof of LAW work_note_apart
# A note's number is a tower of height 0, a result's of height 1 or more
# (LAWork.wt.tower).

import Base
import ../../bend/progress.bend as Pr
import ../../laws/work.bend as Work
import ./base.bend as LWork

def Work.work_note_apart(m, r, x, y):
  (LWork.wt.tower(0n, 0n, x, y), LWork.wt.note_res(x, m, r))
