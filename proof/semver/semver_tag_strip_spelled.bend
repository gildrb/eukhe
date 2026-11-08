# eukhe: the proof of LAW semver_tag_strip_spelled
#
# PROOF of LAW semver_tag_strip_spelled: Tag.strip is the prefix test of
# `eukhe-v` (Tag.after), which answers what follows a text that starts
# with its prefix (each char equals itself: stg.char_refl).

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ./base/tag.bend as LASemverTag

def Semver.semver_tag_strip_spelled(r):
  LASemverTag.pt.after_spelled("eukhe-v", r)
