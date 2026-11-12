# eukhe: the proof of LAW text_pat_hit_complete
#
# PROOF: the found alternative passes the code's prefix test or search
# (LA.tpb.fc, from their completeness), and the code tries every alternative
# before it in turn (LA.tpb.hc, by induction on those before it).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_hit_complete(s, a, pre, its, post, h):
  LA.tpb.hc(a, s, pre, its, post, LA.tpb.fc(a, s, its, h))
