# eukhe: the proof of LAW tags_entry_answers
#
# PROOF: the entry reads the request back whole with nothing left
# (tags_entry_reads) and answers `fates` with an encoder equal to the
# spec's (ptg.reply).

import Base
import ../../bend/doc_tags.bend as Dt
import ../../bend/ffi_doc_tags.bend as FDt
import ../../bend/wire.bend as Wr
import ../../laws/doc_tags.bend as DocTags
import ../../laws/base.bend as LawsBase
import ./base.bend as LADocTags
import ./tags_entry_reads.bend as PTagsEntryReads

def DocTags.tags_entry_answers(ss, h):
  %Equal.sym(Wr.Dec<List<&2, Dt.Scan>>, FDt.get_req(DocTags.sp_w_req(ss, "")), Wr.Got{ss, ""}, DocTags.tags_entry_reads(ss, "", h)) : {FDt.ffi.got(_) == DocTags.sp_w_reply(ss) : String}
  LADocTags.ptg.reply(Dt.fates(ss), "")
