# eukhe: the proof of LAW semver_tag_strip_exact
#
# PROOF of LAW semver_tag_strip_exact: Tag.strip is the prefix test of
# `eukhe-v` (Tag.after); it answers only after each char of the prefix
# compared equal (stg.char_sound), so the text is the prefix then the
# answer (induction on the prefix).

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ./base/tag.bend as LASemverTag

def Semver.semver_tag_strip_exact(t, r, h):
  LASemverTag.pt.after_exact("eukhe-v", t, r, h)
