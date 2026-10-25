# eukhe: the proof of LAW merge_is_one_pair

import Base
import ../../laws/optchat.bend as Optchat
import ./base/step.bend as LA

# (c) A merge

def Optchat.merge_is_one_pair(info, v, a):
  LA.merge_is_one_pair(info, v, a)
