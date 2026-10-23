# eukhe: the proof of LAW theme_pick_cause

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.cause_of(m: Maybe<&2, Nat>) -> {TChoice.cause.of(m) == Theme.th.cause.of(m) : TChoice.Cause}:
  match m:
    case None{}:
      {==}
    case Some{at}:
      {==}

def Theme.theme_pick_cause(ls, n, id, w):
  +want = {Some{Theme.th.cause.of(Theme.th.blame(ls, n, 0n))} : Maybe<&2, TChoice.Cause>}
  %Equal.sym(TChoice.Pick, TChoice.pick(ls, n), TChoice.pick.warn(True{}, id, ls, n), LA.pt.pick_w(ls, n, id, True{}, w)) : {Theme.th.cause(_) == want : Maybe<&2, TChoice.Cause>}
  %Equal.sym(Maybe<&2, Nat>, TChoice.cause.go(ls, n, 0n), Theme.th.blame(ls, n, 0n), LA.pt.cause_go(ls, n, 0n)) : {Some{TChoice.cause.of(_)} == want : Maybe<&2, TChoice.Cause>}
  Equal.cong(TChoice.Cause, Maybe<&2, TChoice.Cause>, x => Some{x}, TChoice.cause.of(Theme.th.blame(ls, n, 0n)), Theme.th.cause.of(Theme.th.blame(ls, n, 0n)), pt.cause_of(Theme.th.blame(ls, n, 0n)))
