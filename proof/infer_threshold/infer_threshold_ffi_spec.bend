# eukhe: the proof of LAW infer_threshold_ffi_spec
# The laws' reader reads every input as the entry does (the projection
# gtm.go of infer_threshold_ffi_malformed_exact); a whole request gets the
# model's plan, which is the spec's (infer_threshold_plan_exact), written
# as the spec writes it (gfa.plan); anything else gets the error form.

import Base
import ../../bend/infer_threshold.bend as M
import ../../bend/ffi_infer_threshold.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/infer_threshold.bend as InferThreshold
import ./infer_threshold_ffi_malformed_exact.bend as PGtm
import ./infer_threshold_ffi_answers.bend as PGfa
import ./infer_threshold_plan_exact.bend as PGPlan

# the entry's answer to a request is the spec's reply to it
def gts.answer(q: FT.Req) -> {FT.answer(q) == InferThreshold.reply_spec(PGtm.gtm.ask(q)) : String}:
  match q:
    case FT.Req{+on, +t, +w, +r, +m, +keep, +full, +xs, +cuts}:
      %InferThreshold.infer_threshold_plan_exact(on, t, w, r, m, keep, full, xs, cuts) : {FT.put_plan(M.plan(on, t, w, r, m, keep, full, xs, cuts)) == InferThreshold.spell_plan(_) : String}
      PGfa.gfa.plan(M.plan(on, t, w, r, m, keep, full, xs, cuts))

def gts.end(b: Bool, q: FT.Req) -> {FT.run.end(b, q) == InferThreshold.entry_spec.of(InferThreshold.read_ask.end(b, PGtm.gtm.ask(q))) : String}:
  match b:
    case True{}:
      gts.answer(q)
    case False{}:
      {==}

def gts.whole(d: Wr.Dec<FT.Req>) -> {FT.run(d) == InferThreshold.entry_spec.of(InferThreshold.read_ask.whole(PGtm.gtm.dec(d))) : String}:
  match d:
    case Wr.Got{q, s}:
      gts.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def InferThreshold.infer_threshold_ffi_spec(s):
  %Equal.sym(Wr.Dec<InferThreshold.Ask>, InferThreshold.read_ask.go(Wr.get_bool(s)), PGtm.gtm.dec(FT.get_req.go(Wr.get_bool(s))), PGtm.gtm.go(Wr.get_bool(s))) : {FT.ffi(s) == InferThreshold.entry_spec.of(InferThreshold.read_ask.whole(_)) : String}
  gts.whole(FT.get_req.go(Wr.get_bool(s)))
