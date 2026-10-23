# eukhe: the proof of LAW tree_rewind_reaches

import Base
import ../../laws/tree.bend as Tree
import ./base/tree/sorted.bend as LATreeSorted

def Tree.tree_rewind_reaches(a, b, ga, gb):
  LATreeSorted.rewind_reaches(a, b, ga, gb)
