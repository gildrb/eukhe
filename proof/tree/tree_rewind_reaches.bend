# eukhe: the proof of LAW tree_rewind_reaches

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.tree_rewind_reaches(a, b, ga, gb):
  LA.rewind_reaches(a, b, ga, gb)
