# eukhe: the proof of LAW irreversible_entry_reads
#
# PROOF: each field of a spelled request reads back, the rest untouched
# (LA.irb.rt).

import Base
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

def Irreversible.irreversible_entry_reads(q, rest, fits):
  LA.irb.rt(q, rest, fits)
