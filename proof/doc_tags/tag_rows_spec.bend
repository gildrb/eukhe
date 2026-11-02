# eukhe: the proof of LAW tag_rows_spec
#
# PROOF: by induction on the text and the selection, `rows` and the spec's
# `sp_rows` cut the same rows (ptg.rows).

import Base
import ../../laws/doc_tags.bend as DocTags
import ./base.bend as LADocTags

def DocTags.tag_rows_spec(ts, sel, n):
  LADocTags.ptg.rows(ts, sel, n)
