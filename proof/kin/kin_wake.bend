# eukhe: the proof of LAW kin_wake
#
# PROOF: case analysis on the state; each landing is the spec's and ends in the inbox.

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK


def Kin.kin_wake(st):
  match st:
    case K.Busy{}:
      ({==}, {==})
    case K.Idle{}:
      ({==}, {==})
    case K.Parked{}:
      ({==}, {==})
