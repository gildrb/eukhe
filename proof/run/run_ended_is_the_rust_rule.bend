# eukhe: the proof of LAW run_ended_is_the_rust_rule
#
# PROOF: case by case (LARunEntry.rex.ended).

import Base
import ../../laws/run/spec.bend as RunSpec
import ./base/entry.bend as LARunEntry

def RunSpec.run_ended_is_the_rust_rule(m):
  LARunEntry.rex.ended(m)
