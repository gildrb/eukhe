# eukhe: the proof of LAW tree_replay_sound

import Base
import ../../laws/tree.bend as Tree
import ./base/tree/sorted.bend as LATreeSorted

def Tree.tree_replay_sound(rs):
  LATreeSorted.replay_sound(rs)
