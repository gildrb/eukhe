# eukhe: the proof of LAW attack_entry_reads
#
# PROOF: the laws' reader is the entry's decoder (LR.ar.req), which reads a
# spelled request back with nothing left (LE.ae.req).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../spec/verified/attack_wire.bend as SAW
import ../../laws/attack.bend as Attack
import ./base/entry.bend as LE
import ./base/read.bend as LR

def Attack.attack_entry_reads(q, fit):
  %LR.ar.req(Wr.get_nat(SAW.w_req(q, ""))) : {SAW.r_whole(_) == Some{q} : Maybe<&2, FA.Req>}
  %LE.ae.req(q, "", fit) : {SAW.r_whole(_) == Some{q} : Maybe<&2, FA.Req>}
  {==}
