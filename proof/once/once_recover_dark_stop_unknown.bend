# eukhe: the proof of LAW once_recover_dark_stop_unknown
#
# PROOF: a dark started effect of a stopped run computes to an interrupt
# for every policy.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once

def Once.once_recover_dark_stop_unknown(again, p):
  match p:
    case O.Never{}:
      {==}
    case O.Safe{}:
      {==}
    case O.Keyed{d, cap}:
      {==}
