# job_notice: whether the end of one settled job wakes its session
# (Rust: eukhe-daemon job_notices.rs JobNotices::deliver, eukhe-core
# durable/rlm/jobs.rs cancel). A job settles after its call stopped
# blocking the turn: a background kernel `bash()` command, a detached
# `python` cell, a `bash` tool script. Its end is news to the agent unless
# the agent itself stopped it (`handle.kill()`) or its own call already
# holds the result (a `jobs.cancel` that saw the job settle within its
# budget takes the result into its reply). News wakes the session: the
# notice is delivered as session input (steered into a busy turn, queued,
# an idle session resumed); anything else is dropped: no input, no row, no
# wake. Pure: no IO, no @unsafe.

import Base

# who stopped the job: nobody (it ended by itself), the agent's own code,
# the user from the bash view, an interrupt (a cancelled one-shot call)
type Stopper is Data:
  NoStop{}
  AgentStop{}
  UserStop{}
  InterruptStop{}

# what becomes of the job's end: dropped, or delivered as a wake
type Notice is Data:
  Drops{}
  Wakes{}

def notice.untaken(by: Stopper) -> Notice:
  match by:
    case NoStop{}:
      Wakes{}
    case AgentStop{}:
      Drops{}
    case UserStop{}:
      Wakes{}
    case InterruptStop{}:
      Wakes{}

# the notice of a job's end: dropped when the agent's own call took the
# result, or when the agent stopped the job; else a wake
def notice(by: Stopper, taken: Bool) -> Notice:
  match taken:
    case True{}:
      Drops{}
    case False{}:
      notice.untaken(by)
