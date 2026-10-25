# eukhe: the proof of LAW retry_idle_req_fits_example
import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LARetryIdle

def RetryIdle.retry_idle_req_fits_example():
  ({==}, {==}, {==})
