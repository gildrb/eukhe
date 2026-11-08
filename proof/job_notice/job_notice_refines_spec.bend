# eukhe: the proof of LAW job_notice_refines_spec
#
# PROOF: the eight inputs; both sides compute.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice

def JobNotice.job_notice_refines_spec(by, taken):
  match by:
    case JN.NoStop{}:
      match taken:
        case True{}:
          {==}
        case False{}:
          {==}
    case JN.AgentStop{}:
      match taken:
        case True{}:
          {==}
        case False{}:
          {==}
    case JN.UserStop{}:
      match taken:
        case True{}:
          {==}
        case False{}:
          {==}
    case JN.InterruptStop{}:
      match taken:
        case True{}:
          {==}
        case False{}:
          {==}
