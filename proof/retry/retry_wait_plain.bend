# eukhe: the proof of LAW retry_wait_plain

import Base
import ../../laws/retry.bend as Retry

def Retry.retry_wait_plain(jitter, cap):
  {==}
