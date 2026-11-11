# eukhe: the proof of LAW call_lift_table_families
#
# PROOF: closed: the shipped table and the stamps compute.

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift

def CallLift.call_lift_table_families():
  ({==}, ({==}, {==}))
