# eukhe: the proof of LAW core_infer_left_over

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_infer.bend as FIn
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_infer_left_over(q, c, rest, h):
  %LA.pc.i_req(q, SCon{c, rest}, h) : {FIn.ffi.go(_) == Wr.err("strict plan request: input left over") : String}
  {==}
