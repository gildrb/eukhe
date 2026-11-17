# eukhe: the proof of LAW strength_entry_reads
#
# PROOF: the laws' reader is the entry's decoder (LR.sr.req), which reads a
# spelled request back with nothing left (LE.se.req).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../spec/verified/strength_wire.bend as SW
import ../../laws/strength.bend as Strength
import ./base/entry.bend as LE
import ./base/read.bend as LR

def Strength.strength_entry_reads(q, fit):
  %LR.sr.req(Wr.get_nat(SW.w_req(q, ""))) : {SW.r_whole(_) == Some{q} : Maybe<&2, FS.Req>}
  %LE.se.req(q, "", fit) : {SW.r_whole(_) == Some{q} : Maybe<&2, FS.Req>}
  {==}
