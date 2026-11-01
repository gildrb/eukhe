# eukhe: the proof of LAW job_notice_entry_is_spec
#
# PROOF: the eight inputs; the entry computes on each spelled request.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice

def JobNotice.job_notice_entry_is_spec(by, taken):
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
