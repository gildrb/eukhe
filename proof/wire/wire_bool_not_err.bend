# eukhe: the proof of LAW wire_bool_not_err

import Base
import ../../laws/wire.bend as Wire

def Wire.wire_bool_not_err(b, rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
