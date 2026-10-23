# eukhe: the proof of LAW nearest_answer_wins

import Base
import ../../laws/approvals.bend as Approvals
import ./base.bend as LA

def Approvals.nearest_answer_wins(below, quiet, yes, above):
  LA.pa.nearest(below, quiet, yes, above)
