# eukhe: the proof of LAW semver_next_not_tagged

import Base
import ../../laws/semver.bend as Semver
import ./base.bend as LA

def Semver.semver_next_not_tagged(s, xs, t, ys, v, parsed):
  LA.ps.next_ne(s, xs, t, ys, v, parsed)
