# eukhe: the proof of LAW semver_roundtrip

import Base
import ../../laws/semver.bend as Semver
import ./base.bend as LA

# (R1) Release versions

def Semver.semver_roundtrip(v):
  LA.ps.roundtrip(v)
