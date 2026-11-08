# durable (spec): what the laws of area job_notice (laws/job_notice.bend)
# speak of, over the types of bend/job_notice.bend: whether the end of one
# settled job wakes its session. A spec: the shipped code never calls it.
#
# S1: the agent already knows a job's end when it stopped the job itself,
#     or when its own call holds the job's result.
# S2: an end the agent already knows is no news: it is dropped (no input,
#     no row, no wake).
# S3: every other end is news and wakes the session: a job that ended by
#     itself, or that the user or an interrupt stopped, and whose result no
#     call of the agent holds. Nothing else is dropped.

import Base
import ../../bend/job_notice.bend as N

# the agent's own code stopped the job (S1)
def by_agent(by: N.Stopper) -> Bool:
  match by:
    case N.NoStop{}:
      False{}
    case N.AgentStop{}:
      True{}
    case N.UserStop{}:
      False{}
    case N.InterruptStop{}:
      False{}

# the agent already knows the job's end (S1)
def knows(by: N.Stopper, taken: Bool) -> Bool:
  Bool.or(by_agent(by), taken)

def of_news(known: Bool) -> N.Notice:
  match known:
    case True{}:
      N.Drops{}
    case False{}:
      N.Wakes{}

# the notice of a job's end: dropped exactly when the agent already knows
# it (S2, S3)
def notice(by: N.Stopper, taken: Bool) -> N.Notice:
  of_news(knows(by, taken))
