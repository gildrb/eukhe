# eukhe: the proof of LAW tags_entry_refuses
#
# PROOF: the entry answers either the error form or a reply, and a reply
# opens with its count, never 'E' (wire_nat_not_err, ptg.reply_not_err).

import Base
import ../../bend/doc_tags.bend as Dt
import ../../bend/ffi_doc_tags.bend as FDt
import ../../bend/wire.bend as Wr
import ../../laws/doc_tags.bend as DocTags
import ../../laws/base.bend as LawsBase
import ./base.bend as LADocTags

def ptr.done(+ss: List<&2, Dt.Scan>, b: Bool, bad: {LawsBase.wire_opens_err(FDt.ffi.done(ss, b)) == True{} : Bool}) -> {FDt.ffi.done(ss, b) == Wr.err("doc_tags: malformed request") : String}:
  match b:
    case True{}:
      LADocTags.ptg.tf({FDt.answer(ss) == Wr.err("doc_tags: malformed request") : String},
        Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FDt.answer(ss)), False{},
          Equal.sym(Bool, LawsBase.wire_opens_err(FDt.answer(ss)), True{}, bad),
          LADocTags.ptg.reply_not_err(Dt.fates(ss), "")))
    case False{}:
      {==}

def ptr.got(d: Wr.Dec<List<&2, Dt.Scan>>, bad: {LawsBase.wire_opens_err(FDt.ffi.got(d)) == True{} : Bool}) -> {FDt.ffi.got(d) == Wr.err("doc_tags: malformed request") : String}:
  match d:
    case Wr.Got{+ss, +r}:
      ptr.done(ss, Wr.end(r), bad)
    case Wr.Bad{}:
      {==}

def DocTags.tags_entry_refuses(s, bad):
  ptr.got(FDt.get_req(s), bad)
