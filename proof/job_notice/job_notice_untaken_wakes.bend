# eukhe: the proof of LAW job_notice_untaken_wakes
#
# PROOF: every stopper; the entry computes on the spelled request; the
# agent's stop refutes the premise.

import Base
import ../../bend/job_notice.bend as JN
import ../../laws/job_notice.bend as JobNotice
import ../../bend/ffi_job_notice.bend as FJn
import ./base.bend as LA

def JobNotice.job_notice_untaken_wakes(by, other):
  match by:
    case JN.NoStop{}:
      {==}
    case JN.AgentStop{}:
      LA.jnb.absurd_tf({FJn.ffi(JobNotice.sp_w_req(JN.AgentStop{}, False{}, "")) == JobNotice.sp_w_reply(JN.Wakes{}) : String}, other)
    case JN.UserStop{}:
      {==}
    case JN.InterruptStop{}:
      {==}
