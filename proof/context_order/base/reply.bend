# eukhe: lemmas of the entry proofs of area context_order: the replies
#
# Every reply encoder of bend/ffi_context_order.bend is the spec's speller
# (laws/context_order.bend spell_*), so the entry's answer is the spelled
# answer of the model (cor.answer), and no answer opens with 'E'
# (cor.not_err).

import Base
import ../../../bend/context_order.bend as Co
import ../../../bend/ffi_context_order.bend as FCo
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/context_order.bend as ContextOrder
import ../base.bend as LACo

def cor.step(x: Co.Step, -rest: String) -> {FCo.put_step(x, rest) == ContextOrder.spell_step(x, rest) : String}:
  match x:
    case Co.Take{i}:
      {==}
    case Co.Miss{i, j}:
      {==}

def cor.steps.items(xs: List<&2, Co.Step>, +rest: String) -> {FCo.put_steps.items(xs, rest) == ContextOrder.spell_steps.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cor.steps.items(t, rest) : {FCo.put_step(x, FCo.put_steps.items(t, rest)) == ContextOrder.spell_step(x, _) : String}
      cor.step(x, FCo.put_steps.items(t, rest))

def cor.steps(+xs: List<&2, Co.Step>, +rest: String) -> {FCo.put_steps(xs, rest) == ContextOrder.spell_steps(xs, rest) : String}:
  Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Co.Step, xs), z), FCo.put_steps.items(xs, rest), ContextOrder.spell_steps.items(xs, rest), cor.steps.items(xs, rest))

def cor.nats.items(xs: List<&2, Nat>, -rest: String) -> {FCo.put_nats.items(xs, rest) == LawsBase.wire_spell_nats.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(String, String, z => Wr.put_nat(x, z), FCo.put_nats.items(t, rest), LawsBase.wire_spell_nats.items(t, rest), cor.nats.items(t, rest))

def cor.nats(+xs: List<&2, Nat>, -rest: String) -> {FCo.put_nats(xs, rest) == LawsBase.wire_spell_nats(xs, rest) : String}:
  Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Nat, xs), z), FCo.put_nats.items(xs, rest), LawsBase.wire_spell_nats.items(xs, rest), cor.nats.items(xs, rest))

def cor.mnat(m: Maybe<&2, Nat>, -rest: String) -> {FCo.put_mnat(m, rest) == ContextOrder.spell_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def cor.plan(p: Co.Plan, +rest: String) -> {FCo.put_plan(p, rest) == ContextOrder.spell_plan(p, rest) : String}:
  match p:
    case Co.Plan{+sp, +n, +xs}:
      %cor.steps(xs, rest) : {FCo.put_mnat(sp, Wr.put_nat(n, FCo.put_steps(xs, rest))) == ContextOrder.spell_mnat(sp, Wr.put_nat(n, _)) : String}
      cor.mnat(sp, Wr.put_nat(n, FCo.put_steps(xs, rest)))

def cor.keep(k: Co.Keep, +rest: String) -> {FCo.put_keep(k, rest) == ContextOrder.spell_keep(k, rest) : String}:
  match k:
    case Co.Omitted{}:
      {==}
    case Co.Own{+js}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FCo.put_nats(js, rest), LawsBase.wire_spell_nats(js, rest), cor.nats(js, rest))
    case Co.Alt{+js}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), FCo.put_nats(js, rest), LawsBase.wire_spell_nats(js, rest), cor.nats(js, rest))

def cor.part(p: Co.Part, +rest: String) -> {FCo.put_part(p, rest) == ContextOrder.spell_part(p, rest) : String}:
  match p:
    case Co.Part{+i, +k}:
      Equal.cong(String, String, z => Wr.put_nat(i, z), FCo.put_keep(k, rest), ContextOrder.spell_keep(k, rest), cor.keep(k, rest))

def cor.parts.items(ps: List<&2, Co.Part>, +rest: String) -> {FCo.put_parts.items(ps, rest) == ContextOrder.spell_parts.items(ps, rest) : String}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cor.parts.items(t, rest) : {FCo.put_part(x, FCo.put_parts.items(t, rest)) == ContextOrder.spell_part(x, _) : String}
      cor.part(x, FCo.put_parts.items(t, rest))

def cor.derived(d: Co.Derived) -> {FCo.put_derived(d) == ContextOrder.spell_derived(d) : String}:
  match d:
    case Co.Derived{+ps, +p}:
      %cor.plan(p, "") : {Wr.put_nat(List.length(&2, Co.Part, ps), FCo.put_parts.items(ps, FCo.put_plan(p, ""))) == Wr.put_nat(List.length(&2, Co.Part, ps), ContextOrder.spell_parts.items(ps, _)) : String}
      Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Co.Part, ps), z), FCo.put_parts.items(ps, FCo.put_plan(p, "")), ContextOrder.spell_parts.items(ps, FCo.put_plan(p, "")), cor.parts.items(ps, FCo.put_plan(p, "")))

def cor.keeps.items(ks: List<&2, List<&2, Nat>>, +rest: String) -> {FCo.put_keeps.items(ks, rest) == ContextOrder.spell_keeps.items(ks, rest) : String}:
  match ks:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cor.keeps.items(t, rest) : {FCo.put_nats(x, FCo.put_keeps.items(t, rest)) == LawsBase.wire_spell_nats(x, _) : String}
      cor.nats(x, FCo.put_keeps.items(t, rest))

def cor.extended(x: Co.Extended) -> {FCo.put_extended(x) == ContextOrder.spell_extended(x) : String}:
  match x:
    case Co.Rederive{}:
      {==}
    case Co.Extended{+ks, +p}:
      %cor.plan(p, "") : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, List<&2, Nat>, ks), FCo.put_keeps.items(ks, FCo.put_plan(p, "")))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, List<&2, Nat>, ks), ContextOrder.spell_keeps.items(ks, _))) : String}
      Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(List.length(&2, List<&2, Nat>, ks), z)), FCo.put_keeps.items(ks, FCo.put_plan(p, "")), ContextOrder.spell_keeps.items(ks, FCo.put_plan(p, "")), cor.keeps.items(ks, FCo.put_plan(p, "")))

# the entry's answer is the spelled answer of the model
def cor.answer(q: FCo.Req) -> {FCo.answer(q) == ContextOrder.spell_reply(q) : String}:
  match q:
    case FCo.QOrder{ms}:
      cor.steps(Co.order(ms), "")
    case FCo.QDerive{mk, es}:
      cor.derived(Co.derive(mk, es))
    case FCo.QExtend{ads, open}:
      cor.extended(Co.extend(ads, open))
    case FCo.QLead{rs}:
      cor.mnat(Co.lead(rs), "")

def cor.ext_ne(x: Co.Extended) -> {LawsBase.wire_opens_err(FCo.put_extended(x)) == False{} : Bool}:
  match x:
    case Co.Rederive{}:
      Wire.wire_nat_not_err(0n, "")
    case Co.Extended{+ks, p}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(List.length(&2, List<&2, Nat>, ks), FCo.put_keeps.items(ks, FCo.put_plan(p, ""))))

def cor.mnat_ne(m: Maybe<&2, Nat>) -> {LawsBase.wire_opens_err(FCo.put_mnat(m, "")) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{n}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(n, ""))

def cor.derived_ne(d: Co.Derived) -> {LawsBase.wire_opens_err(FCo.put_derived(d)) == False{} : Bool}:
  match d:
    case Co.Derived{+ps, p}:
      Wire.wire_nat_not_err(List.length(&2, Co.Part, ps), FCo.put_parts.items(ps, FCo.put_plan(p, "")))

# no answer of the entry opens with 'E'
def cor.not_err(q: FCo.Req) -> {LawsBase.wire_opens_err(FCo.answer(q)) == False{} : Bool}:
  match q:
    case FCo.QOrder{ms}:
      +xs = Co.order(ms)
      Wire.wire_nat_not_err(List.length(&2, Co.Step, xs), FCo.put_steps.items(xs, ""))
    case FCo.QDerive{mk, es}:
      cor.derived_ne(Co.derive(mk, es))
    case FCo.QExtend{ads, open}:
      cor.ext_ne(Co.extend(ads, open))
    case FCo.QLead{rs}:
      cor.mnat_ne(Co.lead(rs))
