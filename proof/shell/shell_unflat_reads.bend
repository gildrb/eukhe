# eukhe: the proof of LAW shell_unflat_reads
# Fl.unflat reads back Fl.flat (LWire.fe.unflat_flat: the fold of a flat
# list stands for the lists it spells).

import Base
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell
import ../base/wire.bend as LWire

def Shell.shell_unflat_reads(xss):
  LWire.fe.unflat_flat(xss)
