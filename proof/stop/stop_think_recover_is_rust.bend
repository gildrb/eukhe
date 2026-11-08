# eukhe: the proof of LAW stop_think_recover_is_rust
#
# PROOF: the count, the window test and the cap test are the spec's; the ladder then matches rung by rung (stb.think_recover).

import Base
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_think_recover_is_rust(long, leak, redirect, repeat, k, row, window, catalog, prompt, out, cuttable, lower):
  LA.stb.think_recover(long, leak, redirect, repeat, k, row, window, catalog, prompt, out, cuttable, lower)
