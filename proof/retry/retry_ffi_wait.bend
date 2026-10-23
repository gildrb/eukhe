# eukhe: the proof of LAW retry_ffi_wait

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def Retry.retry_ffi_wait(base, attempt, cap, draw, server, h):
  +Q = {Fr.QWait{base, attempt, cap, draw, server} : Fr.Req}
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(Fr.put_req(Q, "")), Wr.Got{Q, ""}, LA.rw.req_rt(Q, "", h)) : {Fr.ffi.got(_) == Fr.put_delay(R.retry_wait(base, attempt, cap, draw, server), "") : String}
  {==}
