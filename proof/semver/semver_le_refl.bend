# eukhe: the proof of LAW semver_le_refl

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.semver_le_refl(v):
  LA.semver.ps.le_refl(v)
