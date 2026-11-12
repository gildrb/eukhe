# eukhe: the proof of LAW loop_ffi_st_reads_spelled
#
# PROOF: field by field (le.r_st): each reader stage reads back the value
# its speller wrote, by the round-trip laws of the wire.

import Base
import ../../laws/loop/entry.bend as LoopEntry
import ./base/entry.bend as LALoopEntry

def LoopEntry.loop_ffi_st_reads_spelled(s, rest, h):
  LALoopEntry.le.r_st(s, rest, h)
