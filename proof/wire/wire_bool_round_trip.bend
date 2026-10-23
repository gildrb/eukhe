# eukhe: the proof of LAW wire_bool_round_trip

import Base
import ../../LAWS.bend as Laws

def Laws.wire_bool_round_trip(b, rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
