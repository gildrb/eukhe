# eukhe: the proof of LAW tree_replay_sound

import Base
import ../../laws/tree.bend as Tree
import ./base/tree/sound.bend as LATreeSound

def Tree.tree_replay_sound(rs):
  LATreeSound.replay_sound(rs)
