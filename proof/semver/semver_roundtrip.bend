# eukhe: the proof of LAW semver_roundtrip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

# (R1) Release versions

def Laws.semver_roundtrip(v):
  LA.ps.roundtrip(v)
