# eukhe: the proof of LAW text_pat_class_lit
#
# PROOF: the literal test compares the two codes, and equal codes are equal
# (LQ.shq.eq_sound), so the chars are.

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ../shape/base/chars.bend as LQ

def TextPat.text_pat_class_lit(c, x, h):
  match c x:
    case Chr{+u} Chr{+v}:
      Equal.cong(U32, Char, z => Chr{z}, v, u, Equal.sym(U32, u, v, LQ.shq.eq_sound(u, v, h)))
