# eukhe: the proof of LAW stop_entry_reads
#
# PROOF: a spelled request that fits reads back, the rest untouched (LAStop.stb.req).

import Base
import ../../laws/stop/entry.bend as StopEntry
import ./base.bend as LAStop

def StopEntry.stop_entry_reads(a, rest, h):
  LAStop.stb.req(a, rest, h)
