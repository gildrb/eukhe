# eukhe: the proof of LAW tree_apply_sound

import Base
import ../../laws/tree.bend as Tree
import ../base/retry.bend as LRetry
import ./base/tree/sorted.bend as LATreeSorted

# (S1) The session tree

def Tree.tree_apply_sound(t, LRetry.good, r):
  LATreeSorted.apply_sound(t, LRetry.good, r)
