# eukhe: the proof of LAW job_wait_entry_shut
# The refused state answers its error form before it reads the input.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../laws/job_wait.bend as JobWait

def JobWait.job_wait_entry_shut(i):
  {==}
