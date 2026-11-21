# eukhe: the proof of LAW once_recover_ended_settled
#
# PROOF: by the life: an absent, pending or running life is no end (the
# premise is refuted); a ran, unknown or unstarted one computes to a
# settled.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ./base.bend as LA

def Once.once_recover_ended_settled(l, s, m, p, ended):
  match l:
    case O.Absent{}:
      LA.ob.false_true({O.recover(O.Absent{}, s, m, p) == O.Settled{} : O.Verdict}, ended)
    case O.Pending{}:
      LA.ob.false_true({O.recover(O.Pending{}, s, m, p) == O.Settled{} : O.Verdict}, ended)
    case O.Running{again}:
      LA.ob.false_true({O.recover(O.Running{again}, s, m, p) == O.Settled{} : O.Verdict}, ended)
    case O.Ran{}:
      {==}
    case O.Unsure{}:
      {==}
    case O.Void{}:
      {==}
