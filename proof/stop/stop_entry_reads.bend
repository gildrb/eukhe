# eukhe: the proof of LAW stop_entry_reads
#
# PROOF: the laws' reader is the entry's decoder (sex.ask), which reads a
# spelled request that fits back (LAStop.stb.req).

import Base
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/stop.bend as Stop
import ../../laws/stop/entry.bend as StopEntry
import ./base.bend as LAStop
import ./base/entry.bend as LAStopEntry

def StopEntry.stop_entry_reads(a, rest, h):
  %LAStopEntry.sex.ask(Stop.sp_w_ask(a, rest)) : {_ == Wr.Got{a, rest} : Wr.Dec<FS.Ask>}
  LAStop.stb.req(a, rest, h)
