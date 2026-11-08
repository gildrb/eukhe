# eukhe: the proof of LAW family_text_spec
#
# PROOF: case analysis on the refusal; each text is the spec's text.

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ./base.bend as LF


def Family.family_text_spec(d, m, f):
  match f:
    case F.DepthLimit{}:
      {==}
    case F.FamilyFull{c}:
      {==}
    case F.NoReason{i}:
      {==}
