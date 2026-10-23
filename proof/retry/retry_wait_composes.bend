# eukhe: the proof of LAW retry_wait_composes

import Base
import ../../laws/retry.bend as Retry

def Retry.retry_wait_composes(base, attempt, cap, draw, server):
  {==}
