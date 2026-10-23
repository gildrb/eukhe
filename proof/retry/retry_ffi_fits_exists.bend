# eukhe: the proof of LAW retry_ffi_fits_exists

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../laws/retry.bend as Retry

def Retry.retry_ffi_fits_exists():
  (Fr.QStall{0n}, {==})
