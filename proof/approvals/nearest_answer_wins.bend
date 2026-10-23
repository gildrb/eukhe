# eukhe: the proof of LAW nearest_answer_wins

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.nearest_answer_wins(below, quiet, yes, above):
  LA.pa.nearest(below, quiet, yes, above)
