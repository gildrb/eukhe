# eukhe: the proof of LAW autonomous_asks_iff
#
# PROOF: by cases on the facts (an ended claim by its label, the budget
# and the reading): both sides compute.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/work_left.bend as Wl
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def Autonomous.autonomous_asks_iff(f):
  match f:
    case Au.Facts{on, a, c, b, r}:
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
                  match l:
                    case V.Verified{}:
                      match b:
                        case Au.Working{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
                        case Au.Short{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
                    case V.Failed{}:
                      match b:
                        case Au.Working{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
                        case Au.Short{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
                    case V.Unverified{}:
                      match b:
                        case Au.Working{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
                        case Au.Short{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
                    case V.Passed{}:
                      match b:
                        case Au.Working{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
                        case Au.Short{}:
                          match r:
                            case Wl.Unread{}:
                              {==}
                            case Wl.Finished{}:
                              {==}
                            case Wl.Left{}:
                              {==}
                            case Wl.Unjudged{}:
                              {==}
            case Au.Broken{}:
              {==}
        case False{}:
          {==}
