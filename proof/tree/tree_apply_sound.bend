# eukhe: the proof of LAW tree_apply_sound

import Base
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# (S1) The session tree

def Laws.tree_apply_sound(t, L.good, r):
  LA.apply_sound(t, L.good, r)
