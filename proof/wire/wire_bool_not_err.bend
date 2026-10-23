# eukhe: the proof of LAW wire_bool_not_err

import Base
import ../../LAWS.bend as Laws

def Laws.wire_bool_not_err(b, rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
