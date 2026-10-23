# eukhe: the proof of LAW retry_ffi_stall

import Base
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../bend/ffi_retry.bend as Fr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.retry_ffi_stall(idle, h):
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(Fr.put_req(Fr.QStall{idle}, "")), Wr.Got{Fr.QStall{idle}, ""}, LA.rw.req_rt(Fr.QStall{idle}, "", h)) : {Fr.ffi.got(_) == Wr.put_nat(R.stall.next(idle), "") : String}
  {==}
