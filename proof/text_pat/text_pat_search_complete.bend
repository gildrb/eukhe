# eukhe: the proof of LAW text_pat_search_complete
#
# PROOF: the part passes the prefix test whatever follows
# (text_pat_prefix_complete), and the search tries every suffix (LA.tpb.oc,
# by induction on the text before the part).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA
import ./text_pat_prefix_complete.bend as PTextPatPrefixComplete

def TextPat.text_pat_search_complete(a, u, b, its, h):
  LA.tpb.oc(a, u, b, its, TextPat.text_pat_prefix_complete(u, its, b, h))
