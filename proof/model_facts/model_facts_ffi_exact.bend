# eukhe: the proof of LAW model_facts_ffi_exact
# The entry reads every input as the laws' reader does (mfm.req_go, the
# proof of model_facts_ffi_malformed_exact); on a whole request it answers
# the model's terms, which equal the spec terms (laws/facts.bend
# facts_flag_exact, facts_adaptive_*, facts_effort_exact,
# facts_price_exact, facts_reasoning_exact), spelled alike (mfb.*).

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/model_facts.bend as ModelFacts
import ./base.bend as LMf
import ./model_facts_ffi_malformed_exact.bend as PMfMalformed
import ../facts/facts_flag_exact.bend as PFlagExact
import ../facts/facts_adaptive_compat_first.bend as PAdaptiveFirst
import ../facts/facts_adaptive_rulebook_second.bend as PAdaptiveSecond
import ../facts/facts_effort_exact.bend as PEffortExact
import ../facts/facts_price_exact.bend as PPriceExact
import ../facts/facts_reasoning_exact.bend as PReasoningExact

def mfe.adaptive(c: Maybe<&2, Bool>, +a: If.Ans) -> {Fx.adaptive(c, a) == ModelFacts.mf.adaptive_spec(c, a) : Bool}:
  match c:
    case Some{b}:
      Facts.facts_adaptive_compat_first(b, a)
    case None{}:
      %Facts.facts_flag_exact(a, False{}) : {Fx.adaptive(None{}, a) == _ : Bool}
      Facts.facts_adaptive_rulebook_second(a)

def mfe.answer(q: FMF.Req) -> {FMF.answer(q) == ModelFacts.mf.reply(q) : String}:
  match q:
    case FMF.QFlag{+a, +d}:
      %Facts.facts_flag_exact(a, d) : {Wr.put_bool(Fx.flag(a, d), "") == Wr.put_bool(_, "") : String}
      {==}
    case FMF.QAdaptive{+c, +a}:
      %mfe.adaptive(c, a) : {Wr.put_bool(Fx.adaptive(c, a), "") == Wr.put_bool(_, "") : String}
      {==}
    case FMF.QEffort{+m, +l}:
      %Facts.facts_effort_exact(m, l) : {Wr.put_nat(Fx.effort(m, l), "") == Wr.put_nat(_, "") : String}
      {==}
    case FMF.QPrice{+rows, +m, +t}:
      %Facts.facts_price_exact(rows, m, t) : {FMF.put_mnat(Fx.price(rows, m, t)) == ModelFacts.mf.mnat(_, "") : String}
      LMf.mfb.mnat(Fx.price(rows, m, t))
    case FMF.QReasoning{+x, +e, +l}:
      %Facts.facts_reasoning_exact(x, e, l) : {FMF.put_rfields(Fx.reasoning(x, e, l)) == ModelFacts.mf.rfields(_) : String}
      LMf.mfb.rfields(Fx.reasoning(x, e, l))

def mfe.end(b: Bool, q: FMF.Req) -> {FMF.run.end(b, q) == ModelFacts.mf.spec.go(ModelFacts.mfr.end(b, q)) : String}:
  match b:
    case True{}:
      mfe.answer(q)
    case False{}:
      {==}

def mfe.whole(r: Wr.Dec<FMF.Req>) -> {FMF.run(r) == ModelFacts.mf.spec.go(ModelFacts.mfr.whole(r)) : String}:
  match r:
    case Wr.Got{q, s}:
      mfe.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def ModelFacts.model_facts_ffi_exact(s):
  %PMfMalformed.mfm.req_go(Wr.get_nat(s)) : {FMF.run(_) == ModelFacts.mf.spec.go(ModelFacts.mfr.whole(ModelFacts.mfr.get_req.go(Wr.get_nat(s)))) : String}
  mfe.whole(ModelFacts.mfr.get_req.go(Wr.get_nat(s)))
