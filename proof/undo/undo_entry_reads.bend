# eukhe: the proof of LAW undo_entry_reads
#
# PROOF: each field of a spelled request reads back, the rest untouched
# (LAR.unq.req).

import Base
import ../../laws/undo.bend as Undo
import ./base/reads.bend as LAR

def Undo.undo_entry_reads(q, rest, h):
  LAR.unq.req(q, rest, h)
