# eukhe: the proof of LAW tag_show_spec
#
# PROOF: for a read or a grep, the tag is t on both sides and the rows are
# `rows` of the selection from 1, the spec's (ptg.show, from ptg.rows).

import Base
import ../../laws/doc_tags.bend as DocTags
import ./base.bend as LADocTags

def DocTags.tag_show_spec(t, op):
  LADocTags.ptg.show(t, op)
