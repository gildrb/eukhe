# eukhe: the proof of LAW goal_judge_counts_work

import Base
import ../../bend/progress.bend as Pr
import ../../laws/progress.bend as Progress
import ./base.bend as LA

def Progress.goal_judge_counts_work(hist, seg):
  LA.pp.lt_is_le(Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg)))
