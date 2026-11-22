# eukhe: the proof of LAW path_own_entry_req_exact
#
# PROOF: the decoder stages of path_own_entry_exact (pox.rules) show that
# whatever get_req decodes is the spelling of a request that fits, then
# its rest; h names what it decoded.

import Base
import ../../bend/ffi_path_own.bend as FPo
import ../../bend/wire.bend as Wr
import ../../laws/path_own.bend as PathOwn
import ./path_own_entry_exact.bend as PPox

def PathOwn.path_own_entry_req_exact(s, q, rest, h):
  %h : PPox.pox.Q(s, _)
  PPox.pox.rules(s, FPo.get_ns(s), {==})
