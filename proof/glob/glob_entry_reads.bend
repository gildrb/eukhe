# eukhe: the proof of LAW glob_entry_reads
#
# PROOF: the request's tag, then each field by its wire round trip (every count and length fits by the premise), so each decoder stage hands the next exactly the rest after its field.

import Base
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/entry.bend as GE

def Glob.glob_entry_reads(q, rest, h):
  GE.ge.req(q, rest, h)
