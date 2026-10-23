# eukhe: the proof of LAW wire_bool_round_trip

import Base
import ../../laws/wire.bend as Wire

def Wire.wire_bool_round_trip(b, rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
