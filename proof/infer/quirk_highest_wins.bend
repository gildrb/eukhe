# eukhe: the proof of LAW quirk_highest_wins

import Base
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def Infer.quirk_highest_wins(known, pre, r, post, q, ok, hit, top):
  LA.pq.quirk_highest_wins(known, pre, r, post, q, ok, hit, top)
