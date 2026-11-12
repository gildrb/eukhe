# eukhe: the proof of LAW dash_gate_needs_pairing
#
# PROOF: each frame computes: no pairing is refused at once, and the empty
# text reads as no token (blank).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA

def Dash.dash_gate_needs_pairing(f, b):
  ({==}, ({==}, {==}))
