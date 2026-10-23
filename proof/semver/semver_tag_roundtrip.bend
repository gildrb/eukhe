# eukhe: the proof of LAW semver_tag_roundtrip

import Base
import ../../laws/semver.bend as Semver
import ./base.bend as LA

def Semver.semver_tag_roundtrip(v):
  LA.ps.roundtrip(v)
