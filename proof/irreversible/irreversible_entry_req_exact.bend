# eukhe: the proof of LAW irreversible_entry_req_exact
#
# PROOF: the decoder stages of irreversible_entry_exact (irx.tag) show that
# whatever get_req decodes is the spelling of a request that fits, then
# its rest; h names what it decoded.

import Base
import ../../bend/ffi_irreversible.bend as FIr
import ../../bend/wire.bend as Wr
import ../../laws/irreversible.bend as Irreversible
import ./irreversible_entry_exact.bend as PIrx

def Irreversible.irreversible_entry_req_exact(s, q, rest, h):
  %h : PIrx.irx.Q(s, _)
  PIrx.irx.tag(s, Wr.get_nat(s), {==})
