# eukhe: the proof of LAW wire_bool_spelled
#
# PROOF of LAW wire_bool_spelled: both Bools compute.

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

def Wire.wire_bool_spelled(b, rest):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
