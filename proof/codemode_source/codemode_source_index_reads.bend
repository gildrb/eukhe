# eukhe: the proof of LAW codemode_source_index_reads

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ./base.bend as LACs

# PROOF of LAW codemode_source_index_reads: the key and ',' are the wire spelling of n (wire_nat_decimal), which fits (its digits are the key's at most 10 chars, wire_digits_spells), so the Nat reader reads n back (wire_nat_round_trip), below the cap.

def CodemodeSource.codemode_source_index_reads(k, n, below, short, e):
  LACs.csi.reads(k, n, below, short, e)
