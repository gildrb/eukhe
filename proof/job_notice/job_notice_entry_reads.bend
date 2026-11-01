# eukhe: the proof of LAW job_notice_entry_reads
#
# PROOF: the eight inputs; the decoder reads the one-digit tag and the
# Bool, and the rest is never looked at.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice

def JobNotice.job_notice_entry_reads(by, taken, rest):
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
