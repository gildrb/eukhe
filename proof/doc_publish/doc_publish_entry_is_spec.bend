# eukhe: the proof of LAW doc_publish_entry_is_spec
#
# PROOF: the spelled request reads back whole with nothing left
# (doc_publish_entry_reads), so the entry answers the code's step, which
# is the spec's on every re-read (dpi.step), spelled as the spec spells it.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../bend/ffi_doc_publish.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S
import ./doc_publish_entry_reads.bend as PDocPublishEntryReads

def dpi.moved(lt: Bool) -> {Dp.step.moved(lt) == S.step.moved(lt) : Dp.Step}:
  match lt:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's step is the spec's
def dpi.step(+n: Nat, s: Dp.Seen) -> {Dp.step(n, s) == S.step(n, s) : Dp.Step}:
  match s:
    case Dp.Same{}:
      {==}
    case Dp.Gone{}:
      {==}
    case Dp.Moved{}:
      dpi.moved(Nat.is_lt(n, Dp.bound()))

def dpi.put(p: Dp.Step) -> {FDp.put_step(p) == DocPublish.sp_w_reply(p) : String}:
  match p:
    case Dp.Place{}:
      {==}
    case Dp.Rebase{}:
      {==}
    case Dp.Refuse{}:
      {==}

def DocPublish.doc_publish_entry_is_spec(n, s, h):
  %Equal.sym(Wr.Dec<FDp.Req>, FDp.get_req(DocPublish.sp_w_req(n, s, "")), Wr.Got{FDp.Req{n, s}, ""}, DocPublish.doc_publish_entry_reads(n, s, "", h)) : {FDp.ffi.got(_) == DocPublish.sp_w_reply(S.step(n, s)) : String}
  %Equal.sym(Dp.Step, Dp.step(n, s), S.step(n, s), dpi.step(n, s)) : {FDp.put_step(_) == DocPublish.sp_w_reply(S.step(n, s)) : String}
  dpi.put(S.step(n, s))
