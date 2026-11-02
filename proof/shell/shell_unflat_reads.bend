# eukhe: the proof of LAW shell_unflat_reads
# sh_flat is Fl.flat (shell_flat_spelled), which Fl.unflat reads back (LWire.fe.unflat_flat).

import Base
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell
import ../base/wire.bend as LWire
import ./shell_flat_spelled.bend as PShellFlatSpelled

def Shell.shell_unflat_reads(xss):
  %Shell.shell_flat_spelled(xss) : {Fl.unflat(_) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}
  LWire.fe.unflat_flat(xss)
