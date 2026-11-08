# eukhe: the proof of LAW stop_entry_exact
#
# PROOF: the entry's decoder is the laws' reader stage by stage
# (sex.ask); on a request read whole its answer is the spelled spec
# answer (LAStop.stb.reply); the error texts are the same.

import Base
import ../../laws/stop/entry.bend as StopEntry
import ./base/entry.bend as LAStopEntry

def StopEntry.stop_entry_exact(s):
  LAStopEntry.sex.exact(s)
