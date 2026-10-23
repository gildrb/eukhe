# eukhe: the proof of LAW semver_tag_roundtrip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.semver_tag_roundtrip(v):
  LA.ps.roundtrip(v)
