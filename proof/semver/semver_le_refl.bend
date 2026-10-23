# eukhe: the proof of LAW semver_le_refl

import Base
import ../../laws/semver.bend as Semver
import ./base.bend as LA

def Semver.semver_le_refl(v):
  LA.semver.ps.le_refl(v)
