# eukhe: the proof of LAW verify_entry_reads
#
# PROOF: the laws' reader is the entry's decoder (vr.req), which reads a
# spelled request back with nothing left (ve.req).

import Base
import ../../bend/verify.bend as V
import ../../bend/ffi_verify.bend as FV
import ../../bend/wire.bend as Wr
import ../../spec/verified/verify_wire.bend as SW
import ../../laws/verify.bend as Verify
import ./base/entry.bend as LE
import ./base/read.bend as LR

def Verify.verify_entry_reads(q, fit):
  %LR.vr.req(Wr.get_nat(SW.w_req(q, ""))) : {SW.r_whole(_) == Some{q} : Maybe<&2, FV.Req>}
  %LE.ve.req(q, "", fit) : {SW.r_whole(_) == Some{q} : Maybe<&2, FV.Req>}
  {==}
