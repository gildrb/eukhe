# eukhe: the proof of LAW job_notice_taken_never_wakes
#
# PROOF: every stopper; the entry computes on the spelled request.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice

def JobNotice.job_notice_taken_never_wakes(by):
  match by:
    case JN.NoStop{}:
      {==}
    case JN.AgentStop{}:
      {==}
    case JN.UserStop{}:
      {==}
    case JN.InterruptStop{}:
      {==}
