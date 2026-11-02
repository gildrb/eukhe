# eukhe: the proof of LAW run_ended_is_the_rust_rule
#
# PROOF: case by case (LARunEntry.rex.ended).

import Base
import ../../laws/run/entry.bend as RunEntry
import ./base/entry.bend as LARunEntry

def RunEntry.run_ended_is_the_rust_rule(m):
  LARunEntry.rex.ended(m)
