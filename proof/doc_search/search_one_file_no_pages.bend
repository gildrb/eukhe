# eukhe: the proof of LAW search_one_file_no_pages
#
# PROOF: search_page_answers with multi False: a scope of one file has no
# continuation (0) and no skip past the end (0).

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def DocSearch.search_one_file_no_pages(t, s, k, h):
  DocSearch.search_page_answers(t, s, k, False{}, h)
