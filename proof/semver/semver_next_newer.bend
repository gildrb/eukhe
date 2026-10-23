# eukhe: the proof of LAW semver_next_newer

import Base
import ../../laws/semver.bend as Semver
import ./base.bend as LA

def Semver.semver_next_newer(s, xs, t, ys, v, parsed, ins):
  LA.ps.next_newer(s, xs, t, ys, v, parsed, ins)
