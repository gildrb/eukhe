# eukhe: the proof of LAW autonomous_claim_end_stops
#
# PROOF: the rule reads an ended claim before the budget: both sides compute for every label and budget.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def Autonomous.autonomous_claim_end_stops(l, b):
  match b:
    case Au.Working{}:
      {==}
    case Au.Short{}:
      {==}
