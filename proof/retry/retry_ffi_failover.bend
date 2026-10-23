# eukhe: the proof of LAW retry_ffi_failover

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def Retry.retry_ffi_failover(len, ts, p, h):
  +Q = {Fr.QFailover{len, ts, p} : Fr.Req}
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(Fr.put_req(Q, "")), Wr.Got{Q, ""}, LA.rw.req_rt(Q, "", h)) : {Fr.ffi.got(_) == Fr.put_switch(R.next(len, ts, p), "") : String}
  {==}
