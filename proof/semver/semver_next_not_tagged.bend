# eukhe: the proof of LAW semver_next_not_tagged

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.semver_next_not_tagged(s, xs, t, ys, v, parsed):
  LA.ps.next_ne(s, xs, t, ys, v, parsed)
