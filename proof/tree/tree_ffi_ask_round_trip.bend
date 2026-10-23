# eukhe: the proof of LAW tree_ffi_ask_round_trip

import Base
import ../../laws/tree.bend as Tree
import ./base/wire.bend as LAWire

# The laws
# --------

def Tree.tree_ffi_ask_round_trip(q, rest, h):
  LAWire.tf.ask_rt(q, rest, h)
