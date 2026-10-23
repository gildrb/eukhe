# eukhe: the proof of LAW core_infer_left_over

import Base
import ../../bend/ffi_infer.bend as FIn
import ../../bend/wire.bend as Wr
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def Infer.core_infer_left_over(q, c, rest, h):
  %LA.pc.i_req(q, SCon{c, rest}, h) : {FIn.ffi.go(_) == Wr.err("strict plan request: input left over") : String}
  {==}
