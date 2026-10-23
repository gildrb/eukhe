# eukhe: the proof of LAW theme_pick_cause

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pt.cause_of(m: Maybe<&2, Nat>) -> {T.cause.of(m) == Laws.th.cause.of(m) : T.Cause}:
  match m:
    case None{}:
      {==}
    case Some{at}:
      {==}

def Laws.theme_pick_cause(ls, n, id, w):
  +want = {Some{Laws.th.cause.of(Laws.th.blame(ls, n, 0n))} : Maybe<&2, T.Cause>}
  %Equal.sym(T.Pick, T.pick(ls, n), T.pick.warn(True{}, id, ls, n), LA.pt.pick_w(ls, n, id, True{}, w)) : {Laws.th.cause(_) == want : Maybe<&2, T.Cause>}
  %Equal.sym(Maybe<&2, Nat>, T.cause.go(ls, n, 0n), Laws.th.blame(ls, n, 0n), LA.pt.cause_go(ls, n, 0n)) : {Some{T.cause.of(_)} == want : Maybe<&2, T.Cause>}
  Equal.cong(T.Cause, Maybe<&2, T.Cause>, x => Some{x}, T.cause.of(Laws.th.blame(ls, n, 0n)), Laws.th.cause.of(Laws.th.blame(ls, n, 0n)), pt.cause_of(Laws.th.blame(ls, n, 0n)))
