# eukhe: the proof of LAW grep_skip_class
#
# PROOF: with a match left every skip keeps its reason; with none left
# each reason's class computes.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def DocSearch.grep_skip_class(i, w, p, s, k, r, n):
  ({==}, {==})
