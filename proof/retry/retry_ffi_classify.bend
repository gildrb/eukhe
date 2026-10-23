# eukhe: the proof of LAW retry_ffi_classify

import Base
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../bend/ffi_retry.bend as Fr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.retry_ffi_classify(f, h):
  %Equal.sym(Wr.Dec<Fr.Req>, Fr.get_req(Fr.put_req(Fr.QClassify{f}, "")), Wr.Got{Fr.QClassify{f}, ""}, LA.rw.req_rt(Fr.QClassify{f}, "", h)) : {Fr.ffi.got(_) == Wr.put_bool(R.retryable(f), "") : String}
  {==}
