# eukhe: the proof of LAW run_stream_flag_ignored
#
# PROOF: the flag joins the step only through `Reply.cut`, so a reply the
# cut rejects decides the same with the flag and without it: on both
# sides on_stream takes its cut-arg to `False` (definitionally for a
# reply with no cut, by the bool cases for an error), and both sides are
# the base step.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def flag.plain(+lim: RnDecision.Lim, +t: RnDecision.At) -> {RnDecision.decide.reply(lim, t, RnState.Plain{}, True{}) == RnDecision.decide.reply(lim, t, RnState.Plain{}, False{}) : RnDecision.Then}:
  {==}

def flag.calls(+lim: RnDecision.Lim, +t: RnDecision.At) -> {RnDecision.decide.reply(lim, t, RnState.Calls{}, True{}) == RnDecision.decide.reply(lim, t, RnState.Calls{}, False{}) : RnDecision.Then}:
  {==}

def flag.deferred(+lim: RnDecision.Lim, +t: RnDecision.At) -> {RnDecision.decide.reply(lim, t, RnState.Deferred{}, True{}) == RnDecision.decide.reply(lim, t, RnState.Deferred{}, False{}) : RnDecision.Then}:
  {==}

# an error's cut is `retryable and not noted`, so the flag without the cut
# is `False` on both sides whatever the two bools are
def flag.error(+lim: RnDecision.Lim, +t: RnDecision.At, +retryable: Bool, +noted: Bool) -> {RnDecision.decide.reply(lim, t, RnState.Error{retryable, noted}, Bool.not(RnDecision.Reply.cut(RnState.Error{retryable, noted}))) == RnDecision.decide.reply(lim, t, RnState.Error{retryable, noted}, False{}) : RnDecision.Then}:
  match retryable noted:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def flag.over(+lim: RnDecision.Lim, +t: RnDecision.At, +cut: Bool) -> {RnDecision.decide.reply(lim, t, RnState.Overflow{cut}, True{}) == RnDecision.decide.reply(lim, t, RnState.Overflow{cut}, False{}) : RnDecision.Then}:
  {==}

def Run.run_stream_flag_ignored(l, t, retryable, noted, cut):
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most, +streams}:
      match t:
        case RnDecision.At{+attempt, +notes, +spent, +waited, +compacted}:
          +lim = {RnDecision.Lim{rounds, wait, retries, most, streams} : RnDecision.Lim}
          +at = {RnDecision.At{attempt, notes, spent, waited, compacted} : RnDecision.At}
          (flag.plain(lim, at), flag.calls(lim, at), flag.deferred(lim, at), flag.error(lim, at, retryable, noted), flag.over(lim, at, cut))
