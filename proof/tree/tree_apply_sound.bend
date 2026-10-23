# eukhe: the proof of LAW tree_apply_sound

import Base
import ../../laws/tree.bend as Tree
import ../base/retry.bend as LRetry
import ./base/tree/sound.bend as LATreeSound

# (S1) The session tree

def Tree.tree_apply_sound(t, LRetry.good, r):
  LATreeSound.apply_sound(t, LRetry.good, r)
