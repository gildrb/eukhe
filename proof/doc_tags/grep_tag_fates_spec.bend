# eukhe: the proof of LAW grep_tag_fates_spec
#
# PROOF: file by file, `fate` and the spec's `sp_fate` agree on every scan
# (ptg.fate); the lists follow by induction (ptg.fates).

import Base
import ../../bend/doc_tags.bend as Dt
import ../../bend/ffi_doc_tags.bend as FDt
import ../../bend/wire.bend as Wr
import ../../laws/doc_tags.bend as DocTags
import ../../laws/base.bend as LawsBase
import ./base.bend as LADocTags

def DocTags.grep_tag_fates_spec(ss):
  LADocTags.ptg.fates(ss)
