# eukhe: the proof of LAW tiny_seat_adopts_live
#
# PROOF: both steps compute: the lock held makes the seat ping, and a
# seat adopts on any pong without reading its tag.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/elect.bend as TinyElect

def TinyElect.tiny_seat_adopts_live(m, t):
  ({==}, {==})
