# eukhe: the proof of LAW text_pat_class_lit_self
#
# PROOF: the literal test compares the two codes, and every code equals
# itself (LQ.shq.u32_refl).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ../shape/base/chars.bend as LQ

def TextPat.text_pat_class_lit_self(c):
  match c:
    case Chr{+u}:
      LQ.shq.u32_refl(u)
