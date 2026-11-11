# eukhe: the proof of LAW tag_show_reads
#
# PROOF: both arms of `show` compute the same result from t and sel; the
# later text is not read.

import Base
import ../../bend/doc_tags.bend as Dt
import ../../laws/doc_tags.bend as DocTags

def DocTags.tag_show_reads(t, sel, later):
  ({==}, {==})
