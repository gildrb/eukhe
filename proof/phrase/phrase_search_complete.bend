# eukhe: the proof of LAW phrase_search_complete
#
# PROOF: the part and the text after pass the prefix test
# (phrase_prefix_complete); the flag after the text before is the spec's
# start edge (LA.phb.start), so True; the search walks the text before and
# finds the part there (LA.phb.oc).

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ./base.bend as LA
import ./phrase_prefix_complete.bend as PPhrasePrefixComplete

def Phrase.phrase_search_complete(a, u, b, st, its, en, h, hs, he):
  +e = Phrase.phrase_prefix_complete(u, its, b, en, h, he)
  +hm = Equal.trans(Bool, LA.phb.may_at(a, st, True{}), Phrase.sp_start_ok(st, a), True{}, LA.phb.start(st, a), hs)
  LA.phb.oc(a, String.append(u, b), st, its, en, True{}, hm, e)
