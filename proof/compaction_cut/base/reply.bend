# eukhe: lemmas of the entry proofs of area compaction_cut: the replies
#
# The entry's encoders are the spec's spellers (laws/compaction_cut.bend
# spell_outcome, laws/context_order.bend spell_mnat), so its answer is the
# spelled answer of the model (ccr.answer), and no answer opens with 'E'
# (ccr.not_err).

import Base
import ../../../bend/context_order.bend as Co
import ../../../bend/ffi_context_order.bend as FCo
import ../../../bend/compaction_cut.bend as Cc
import ../../../bend/ffi_compaction_cut.bend as FCc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/context_order.bend as ContextOrder
import ../../../laws/compaction_cut.bend as CompactionCut
import ../../context_order/base.bend as LACo
import ../../context_order/base/read.bend as LACoRead
import ../../context_order/base/exact.bend as LACoExact
import ../../context_order/base/reply.bend as LACoReply

def ccr.outcome(o: Cc.Outcome) -> {FCc.put_outcome(o) == CompactionCut.spell_outcome(o) : String}:
  match o:
    case Cc.Summary{}:
      {==}
    case Cc.Failed{x}:
      {==}

# the entry's answer is the spelled answer of the model
def ccr.answer(q: FCc.Req) -> {FCc.answer(q) == CompactionCut.spell_reply(q) : String}:
  match q:
    case FCc.QCut{h, l, cs}:
      LACoReply.cor.mnat(Cc.cut(h, l, cs), "")
    case FCc.QSummary{s, c, x, e}:
      ccr.outcome(Cc.summary(s, c, x, e))

def ccr.outcome_ne(o: Cc.Outcome) -> {LawsBase.wire_opens_err(FCc.put_outcome(o)) == False{} : Bool}:
  match o:
    case Cc.Summary{}:
      Wire.wire_nat_not_err(0n, "")
    case Cc.Failed{x}:
      Wire.wire_nat_not_err(1n, Wr.put_str(x, ""))

# no answer of the entry opens with 'E'
def ccr.not_err(q: FCc.Req) -> {LawsBase.wire_opens_err(FCc.answer(q)) == False{} : Bool}:
  match q:
    case FCc.QCut{h, l, cs}:
      LACoReply.cor.mnat_ne(Cc.cut(h, l, cs))
    case FCc.QSummary{s, c, x, e}:
      ccr.outcome_ne(Cc.summary(s, c, x, e))
