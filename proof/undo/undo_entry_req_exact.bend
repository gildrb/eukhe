# eukhe: the proof of LAW undo_entry_req_exact
#
# PROOF: the decoder stages of undo_entry_exact (unx.tag) show that
# whatever get_req decodes is the spelling of a request that fits, then
# its rest; h names what it decoded.

import Base
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/undo.bend as Undo
import ./undo_entry_exact.bend as PUnx

def Undo.undo_entry_req_exact(s, q, rest, h):
  %h : PUnx.unx.RP(s, _)
  PUnx.unx.tag(s, Wr.get_nat(s), {==})
