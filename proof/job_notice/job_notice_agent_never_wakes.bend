# eukhe: the proof of LAW job_notice_agent_never_wakes
#
# PROOF: both values of taken; the entry computes on the spelled request.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice

def JobNotice.job_notice_agent_never_wakes(taken):
  match taken:
    case True{}:
      {==}
    case False{}:
      {==}
