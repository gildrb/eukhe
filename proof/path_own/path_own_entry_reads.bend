# eukhe: the proof of LAW path_own_entry_reads
#
# PROOF: each field of a spelled request reads back, the rest untouched
# (LA.po.rt).

import Base
import ../../laws/path_own.bend as PathOwn
import ./base.bend as LA

def PathOwn.path_own_entry_reads(q, rest, fits):
  LA.po.rt(q, rest, fits)
