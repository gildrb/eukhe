# eukhe: the proof of LAW tree_ffi_ask_round_trip

import Base
import ../../laws/tree.bend as Tree
import ./base.bend as LA

# The laws
# --------

def Tree.tree_ffi_ask_round_trip(q, rest, h):
  LA.tf.ask_rt(q, rest, h)
