# eukhe: the proof of LAW tag_from_text_spec
#
# PROOF: row by row, `is_line` is the spec's `sp_line` (ptg.line), and the
# conjunction follows by induction on the rows (ptg.from_text).

import Base
import ../../laws/doc_tags.bend as DocTags
import ./base.bend as LADocTags

def DocTags.tag_from_text_spec(t, rs):
  LADocTags.ptg.from_text(t, rs)
