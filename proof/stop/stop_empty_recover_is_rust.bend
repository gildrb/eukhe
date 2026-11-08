# eukhe: the proof of LAW stop_empty_recover_is_rust
#
# PROOF: the count is the spec's row and the model's cap test is Nat's; the recovery computes (stb.empty_recover).

import Base
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_empty_recover_is_rust(rc, k, row):
  LA.stb.empty_recover(rc, k, row)
