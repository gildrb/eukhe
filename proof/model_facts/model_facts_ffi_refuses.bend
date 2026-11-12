# eukhe: the proof of LAW model_facts_ffi_refuses
#
# PROOF: the entry answers either a decision, which opens with a Bool or a
# Nat (never 'E': wire_bool_not_err, wire_nat_not_err), or the one error
# form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/model_facts.bend as ModelFacts
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../wire/base/spell.bend as LAWireSpell

def mfx.mnat_ok(m: Maybe<&2, Nat>) -> {LawsBase.wire_opens_err(FMF.put_mnat(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{k}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(k, ""))

def mfx.rfields_ok(f: Fx.RFields) -> {LawsBase.wire_opens_err(FMF.put_rfields(f)) == False{} : Bool}:
  match f:
    case Fx.RThinking{}:
      Wire.wire_nat_not_err(1n, "")
    case Fx.RNested{e}:
      Wire.wire_nat_not_err(2n, Wr.put_nat(e, ""))

# no decision opens with 'E'
def mfx.answer_ok(q: FMF.Req) -> {LawsBase.wire_opens_err(FMF.answer(q)) == False{} : Bool}:
  match q:
    case FMF.QFlag{a, d}:
      Wire.wire_bool_not_err(Fx.flag(a, d), "")
    case FMF.QAdaptive{c, a}:
      Wire.wire_bool_not_err(Fx.adaptive(c, a), "")
    case FMF.QEffort{m, l}:
      Wire.wire_nat_not_err(Fx.effort(m, l), "")
    case FMF.QPrice{rows, m, t}:
      mfx.mnat_ok(Fx.price(rows, m, t))
    case FMF.QReasoning{x, e, l}:
      mfx.rfields_ok(Fx.reasoning(x, e, l))

def mfx.refuse(d: Wr.Dec<FMF.Req>, bad: {LawsBase.wire_opens_err(FMF.run(d)) == True{} : Bool}) -> {FMF.run(d) == Wr.err("model facts: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LAWireSpell.ws_absurd({FMF.answer(q) == Wr.err("model facts: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FMF.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FMF.answer(q)), True{}, bad), mfx.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def ModelFacts.model_facts_ffi_refuses(s, bad):
  mfx.refuse(FMF.get_req(s), bad)
