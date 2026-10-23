# eukhe: the proof of LAW tree_rewind_reaches

import Base
import ../../laws/tree.bend as Tree
import ./base.bend as LA

def Tree.tree_rewind_reaches(a, b, ga, gb):
  LA.rewind_reaches(a, b, ga, gb)
