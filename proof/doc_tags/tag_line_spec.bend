# eukhe: the proof of LAW tag_line_spec
#
# PROOF: no line 0; line 1 + m is the lookup at index m, which follows the
# spec's `sp_at` by induction on the text (ptg.line, ptg.at).

import Base
import ../../laws/doc_tags.bend as DocTags
import ./base.bend as LADocTags

def DocTags.tag_line_spec(t, n, x):
  LADocTags.ptg.line(t, n, x)
