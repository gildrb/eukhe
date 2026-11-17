# eukhe: the proof of LAW autonomous_continues_iff
#
# PROOF: by cases on the facts: both sides compute.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def Autonomous.autonomous_continues_iff(f):
  match f:
    case Au.Facts{on, a, c, b}:
      match on:
        case True{}:
          match a:
            case Au.Settled{}:
              match c:
                case Au.Unchecked{}:
                  match b:
                    case Au.Working{}:
                      {==}
                    case Au.Short{}:
                      {==}
                case Au.Returned{}:
                  match b:
                    case Au.Working{}:
                      {==}
                    case Au.Short{}:
                      {==}
                case Au.Ended{l}:
                  match b:
                    case Au.Working{}:
                      {==}
                    case Au.Short{}:
                      {==}
            case Au.Broken{}:
              {==}
        case False{}:
          {==}
