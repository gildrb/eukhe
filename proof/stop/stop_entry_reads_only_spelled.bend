# eukhe: the proof of LAW stop_entry_reads_only_spelled
#
# PROOF: whatever the reader answers, a request it read is the input spelled (LAE.sre.tag, field by field); the premise names that answer.

import Base
import ../../bend/wire.bend as Wr
import ../../laws/stop/entry.bend as StopEntry
import ./base/entry.bend as LAE

def StopEntry.stop_entry_reads_only_spelled(s, a, rest, h):
  %h : LAE.sre.Q(_, s)
  LAE.sre.tag(s, Wr.get_nat(s), {==})
