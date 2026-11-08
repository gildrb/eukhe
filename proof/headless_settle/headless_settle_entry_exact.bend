# eukhe: the proof of LAW headless_settle_entry_exact
#
# PROOF: the entry reads every input as the laws' reader does (hs.req); a
# request read whole is answered with the model's decision, which is the
# spec's (headless_settle_refines_spec), spelled as the spec spells it
# (hs.put); any other input gets the error form on both sides.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/ffi_headless_settle.bend as FHs
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless.bend as Sp
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle
import ./headless_settle_refines_spec.bend as PHeadlessSettleRefinesSpec
import ./headless_settle_entry_answers.bend as PHeadlessSettleEntryAnswers

def hse.end(e: Bool, +f: Hs.Facts) -> {FHs.ffi.done(f, e) == HeadlessSettle.settle_entry.whole(SpW.r_settle_whole.end(e, f)) : String}:
  match e:
    case True{}:
      %Equal.sym(Hs.Settle, Hs.settle(f), Sp.settle_spec(f), HeadlessSettle.headless_settle_refines_spec(f)) : {FHs.put_settle(_, "") == SpW.w_settle(Sp.settle_spec(f), "") : String}
      PHeadlessSettleEntryAnswers.hs.put(Sp.settle_spec(f), "")
    case False{}:
      {==}

def hse.whole(r: Wr.Dec<Hs.Facts>) -> {FHs.ffi.got(r) == HeadlessSettle.settle_entry.whole(SpW.r_settle_whole(r)) : String}:
  match r:
    case Wr.Got{f, +s}:
      hse.end(Wr.end(s), f)
    case Wr.Bad{}:
      {==}

def HeadlessSettle.headless_settle_entry_exact(s):
  %Equal.sym(Wr.Dec<Hs.Facts>, FHs.get_facts(s), SpW.r_settle(s), LAHeadlessSettle.hs.req(s)) : {FHs.ffi.got(_) == HeadlessSettle.settle_entry(s) : String}
  hse.whole(SpW.r_settle(s))
