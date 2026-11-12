# eukhe: the proof of LAW wire_err_never_value
#
# PROOF: 'E' is no digit and neither T nor F: each reader refuses the
# first char (computes, whatever the text).

import Base
import ../../laws/wire.bend as Wire

def Wire.wire_err_never_value(text):
  {==}
