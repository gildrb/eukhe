# eukhe: the proof of LAW semver_next_in_series

import Base
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_next_in_series: Rel.next keeps the series' major and
# minor and sets only the patch; both compare equal to themselves
# (ps.series_next).

def Semver.semver_next_in_series(s, tags):
  LASemver.ps.series_next(s, tags)
