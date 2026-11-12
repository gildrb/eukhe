# eukhe: the proof of LAW text_pat_any_complete
#
# PROOF: the found alternative makes its pattern found (LA.tpb.fc,
# LA.tpb.hc), and the code tries every pattern before it in turn (LA.tpb.ac,
# by induction on those before it).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_any_complete(s, pre, a, apre, its, apost, post, h):
  LA.tpb.ac(s, pre, a, apre, its, apost, post, LA.tpb.hc(a, s, apre, its, apost, LA.tpb.fc(a, s, its, h)))
