# eukhe: the proof of LAW semver_next_newer

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.semver_next_newer(s, xs, t, ys, v, parsed, ins):
  LA.ps.next_newer(s, xs, t, ys, v, parsed, ins)
