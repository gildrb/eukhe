# eukhe: the proof of LAW tiny_run_launch_ended
#
# PROOF: a case per start: each step then computes (an adopted launch
# and a failed one read the start only to decide alike).

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/elect.bend as TinyElect

def TinyElect.tiny_run_launch_ended(m, f):
  match f:
    case Tn.First{}:
      ({==}, ({==}, ({==}, {==})))
    case Tn.Again{}:
      ({==}, ({==}, ({==}, {==})))
