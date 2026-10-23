# eukhe: lemmas the proofs of area admission share: maybe

import Base
import ../../../bend/admission.bend as Ad

# ticket mb with status x
def ad.set(mb: Maybe<&2, Ad.Tk>, x: Ad.Sts) -> Maybe<&2, Ad.Tk>:
  match mb:
    case None{}:
      None{}
    case Some{Ad.Tk{c, s}}:
      Some{Ad.Tk{c, x}}

# Finding, setting and dropping a ticket by its number
# ----------------------------------------------------

# the status of a model ticket as the live controller finds it
def al.st(m: Maybe<&2, Ad.Tk>) -> Maybe<&2, Ad.Sts>:
  match m:
    case None{}:
      None{}
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      Some{Ad.Queued{}}
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      Some{Ad.Granted{}}
    case Some{Ad.Tk{c, Ad.Held{}}}:
      Some{Ad.Held{}}
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      Some{Ad.Preempted{}}
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      None{}
