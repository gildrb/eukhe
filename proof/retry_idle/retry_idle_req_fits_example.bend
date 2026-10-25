# eukhe: the proof of LAW retry_idle_req_fits_example
# A closed claim: both sides compute.

import Base
import ../../laws/retry_idle.bend as RetryIdle

def RetryIdle.retry_idle_req_fits_example():
  ({==}, {==})
