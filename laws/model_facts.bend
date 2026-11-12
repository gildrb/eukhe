# eukhe: the laws of area model_facts

import Base
import ../bend/facts.bend as Fx
import ../bend/ffi_model_facts.bend as FMF
import ../bend/infer.bend as If
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- model_facts ----

# (S6.10) The entry of the model facts: bend/ffi_model_facts.bend
# (the laws of area facts, laws/facts/, pin the model terms it calls)
# ----------------------------------------------------------------
# Rust gathers the rulebook's answers, the compat flag, the env flag, the
# thinking-level map (a wire string as the code 0) and the price rows of
# the model's provider and API (this model 0, another 1; this tier 0,
# another 1; the row's index as its multiplier); the model decides. The
# spellers write what Rust writes with the wire primitives only (the
# grammar of the header of bend/ffi_model_facts.bend, the Rust writer
# crates/eukhe-bend/src/rules/model_facts.rs and WIRE.md).
#
# Requirements:
#   R1  each request Rust spells (a flag, adaptive thinking, the Bedrock
#       effort, a tier's price, the Bedrock reasoning fields), its numbers
#       within the wire, answers the model's decision on it:
#       model_facts_ffi_flag_unknown_default, _flag_known (S6.10.1: a flag
#       is true only at a known 1, an unknown one the wire API's default),
#       model_facts_ffi_adaptive, _effort, _price, _reasoning
#   R2  the entry answers a value only for an input that is exactly one
#       such request: model_facts_ffi_reads_only_requests
#   R3  every other input answers exactly the error form `E model facts:
#       malformed request`: model_facts_ffi_refuses with R2
# Anchors: model_facts_ffi_example, model_facts_ffi_reasoning_example.

def mf.ans(a: If.Ans, rest: String) -> String:
  match a:
    case If.Known{v}:
      Wr.put_nat(0n, Wr.put_nat(v, rest))
    case If.Unknown{}:
      Wr.put_nat(1n, rest)

def mf.mbool(m: Maybe<&2, Bool>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))

def mf.ent(e: Maybe<&2, Maybe<&2, Nat>>, rest: String) -> String:
  match e:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{w}:
      match w:
        case None{}:
          Wr.put_nat(1n, Wr.put_nat(0n, rest))
        case Some{v}:
          Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_nat(v, rest)))

def mf.elv(l: Fx.ELv, rest: String) -> String:
  match l:
    case Fx.EMinimal{}:
      Wr.put_nat(0n, rest)
    case Fx.ELow{}:
      Wr.put_nat(1n, rest)
    case Fx.EMedium{}:
      Wr.put_nat(2n, rest)
    case Fx.EHigh{}:
      Wr.put_nat(3n, rest)
    case Fx.EXhigh{}:
      Wr.put_nat(4n, rest)
    case Fx.EMax{}:
      Wr.put_nat(5n, rest)

def mf.map(m: Fx.EMap, rest: String) -> String:
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      mf.ent(mi, mf.ent(lo, mf.ent(me, mf.ent(hi, mf.ent(xh, mf.ent(mx, rest))))))

def mf.mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))

def mf.row(r: Fx.PRow, rest: String) -> String:
  match r:
    case Fx.PRow{m, t, k}:
      mf.mnat(m, Wr.put_nat(t, Wr.put_nat(k, rest)))

def mf.items(rows: List<&2, Fx.PRow>, rest: String) -> String:
  match rows:
    case Nil{}:
      rest
    case r <> more:
      mf.row(r, mf.items(more, rest))

# the requests Rust writes
def spell_flag(a: If.Ans, d: Bool) -> String:
  Wr.put_nat(0n, mf.ans(a, Wr.put_bool(d, "")))

def spell_adaptive(c: Maybe<&2, Bool>, a: If.Ans) -> String:
  Wr.put_nat(1n, mf.mbool(c, mf.ans(a, "")))

def spell_effort(m: Fx.EMap, l: Fx.ELv) -> String:
  Wr.put_nat(2n, mf.map(m, mf.elv(l, "")))

def spell_price(+rows: List<&2, Fx.PRow>, m: Nat, t: Nat) -> String:
  Wr.put_nat(3n, Wr.put_nat(List.length(&2, Fx.PRow, rows), mf.items(rows, Wr.put_nat(m, Wr.put_nat(t, "")))))

def mf.shape(s: Maybe<&2, Fx.Shape>, rest: String) -> String:
  match s:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      match x:
        case Fx.SClaude{}:
          Wr.put_nat(1n, rest)
        case Fx.SGpt{}:
          Wr.put_nat(2n, rest)

def spell_reasoning(s: Maybe<&2, Fx.Shape>, e: Maybe<&2, Maybe<&2, Nat>>, l: Fx.ELv) -> String:
  Wr.put_nat(4n, mf.shape(s, mf.ent(e, mf.elv(l, ""))))

# the reply Rust reads: 1 the thinking block | 2 then the nested effort
def mf.rfields(f: Fx.RFields) -> String:
  match f:
    case Fx.RThinking{}:
      Wr.put_nat(1n, "")
    case Fx.RNested{e}:
      Wr.put_nat(2n, Wr.put_nat(e, ""))

# every number Rust writes fits the wire
def mf.ans_fits(a: If.Ans) -> Bool:
  match a:
    case If.Known{v}:
      LawsBase.wire_fits(v)
    case If.Unknown{}:
      True{}

def mf.ent_fits(e: Maybe<&2, Maybe<&2, Nat>>) -> Bool:
  match e:
    case None{}:
      True{}
    case Some{w}:
      LawsBase.wire_mfits(w)

def mf.map_fits(m: Fx.EMap) -> Bool:
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      Bool.and(mf.ent_fits(mi), Bool.and(mf.ent_fits(lo), Bool.and(mf.ent_fits(me), Bool.and(mf.ent_fits(hi), Bool.and(mf.ent_fits(xh), mf.ent_fits(mx))))))

def mf.rows_fit(rows: List<&2, Fx.PRow>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case r <> more:
      match r:
        case Fx.PRow{m, t, k}:
          Bool.and(LawsBase.wire_mfits(m), Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(k), mf.rows_fit(more))))

def mf.price_fits(+rows: List<&2, Fx.PRow>, m: Nat, t: Nat) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Fx.PRow, rows)), Bool.and(mf.rows_fit(rows), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(t))))

# a request as Rust spells it, by its kind
def mf.spell(q: FMF.Req) -> String:
  match q:
    case FMF.QFlag{a, d}:
      spell_flag(a, d)
    case FMF.QAdaptive{c, a}:
      spell_adaptive(c, a)
    case FMF.QEffort{m, l}:
      spell_effort(m, l)
    case FMF.QPrice{rows, m, t}:
      spell_price(rows, m, t)
    case FMF.QReasoning{x, e, l}:
      spell_reasoning(x, e, l)

# every number of the request q fits the wire
def mf.fits(q: FMF.Req) -> Bool:
  match q:
    case FMF.QFlag{a, d}:
      mf.ans_fits(a)
    case FMF.QAdaptive{c, a}:
      mf.ans_fits(a)
    case FMF.QEffort{m, l}:
      mf.map_fits(m)
    case FMF.QPrice{rows, m, t}:
      mf.price_fits(rows, m, t)
    case FMF.QReasoning{x, e, l}:
      mf.ent_fits(e)

# LAW model_facts_ffi_reads_only_requests (R2): an answer that is not the
# error form comes from an input that is exactly one request as Rust
# spells it (a flag, adaptive thinking, the effort, the price or the
# reasoning fields), every number within the wire; the laws above give its
# answer
# EXCLUDES: a decoder that accepts an unknown tag (request, answer, compat
#   flag, entry, level, model, shape), a short or missing field, a number
#   past the wire, a row count other than the rows that follow, or input
#   left over, and answers it anyway (a default instead of the error form)
law model_facts_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FMF.ffi(s)) == False{} : Bool}
  exs q: FMF.Req
  {s == mf.spell(q) : String} & {mf.fits(q) == True{} : Bool}

# LAW model_facts_ffi_refuses (R3): every error the entry answers is
# exactly `E model facts: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law model_facts_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FMF.ffi(s)) == True{} : Bool}
  {FMF.ffi(s) == Wr.err("model facts: malformed request") : String}

# LAW model_facts_ffi_flag_unknown_default (S6.10.1): a flag request whose
# rulebook answer is unknown (no rule applies to the model) answers the
# wire API's default d, true or false
# EXCLUDES: an unknown flag always false (or always true), the default
#   ignored or flipped when no rule applies
law model_facts_ffi_flag_unknown_default:
  for +d: Bool
  {FMF.ffi(spell_flag(If.Unknown{}, d)) == Wr.put_bool(d, "") : String}

# LAW model_facts_ffi_flag_known (S6.10.1): a flag request whose rulebook
# answer is a known value v (within the wire) answers true exactly when v
# is 1, whatever the wire API's default d: the default never overrides a
# known answer
# EXCLUDES: the default answered over a known value, a known value other
#   than 1 read as true, a known 1 read as false
law model_facts_ffi_flag_known:
  for +v: Nat
  for +d: Bool
  for fits: {LawsBase.wire_fits(v) == True{} : Bool}
  {FMF.ffi(spell_flag(If.Known{v}, d)) == Wr.put_bool(Nat.is_eq(v, 1n), "") : String}

# LAW model_facts_ffi_adaptive: an adaptive-thinking request answers the model's decision: the compat flag, else the rulebook, else false
law model_facts_ffi_adaptive:
  for +c: Maybe<&2, Bool>
  for +a: If.Ans
  for fits: {mf.ans_fits(a) == True{} : Bool}
  {FMF.ffi(spell_adaptive(c, a)) == Wr.put_bool(Fx.adaptive(c, a), "") : String}

# LAW model_facts_ffi_effort: an effort request answers the model's Bedrock effort for the map and level
law model_facts_ffi_effort:
  for +m: Fx.EMap
  for +l: Fx.ELv
  for +fits: {mf.map_fits(m) == True{} : Bool}
  {FMF.ffi(spell_effort(m, l)) == Wr.put_nat(Fx.effort(m, l), "") : String}

# LAW model_facts_ffi_price: a price request answers the model's row for the model and tier (none: 0, else 1 then it)
law model_facts_ffi_price:
  for +rows: List<&2, Fx.PRow>
  for +m: Nat
  for +t: Nat
  for +fits: {mf.price_fits(rows, m, t) == True{} : Bool}
  {FMF.ffi(spell_price(rows, m, t)) == mf.mnat(Fx.price(rows, m, t), "") : String}

# LAW model_facts_ffi_reasoning: a reasoning request answers the model's Bedrock reasoning fields for the shape, the map's entry and the level
# EXCLUDES: the shape, the entry or the level misread; the nested effort
#   answered as the thinking block or the other way round
law model_facts_ffi_reasoning:
  for +s: Maybe<&2, Fx.Shape>
  for +e: Maybe<&2, Maybe<&2, Nat>>
  for +l: Fx.ELv
  for fits: {mf.ent_fits(e) == True{} : Bool}
  {FMF.ffi(spell_reasoning(s, e, l)) == mf.rfields(Fx.reasoning(s, e, l)) : String}

# LAW model_facts_ffi_example: anchor: the bytes Rust sends and reads: an unknown answer with the default false, a known 1; a compat flag over the rulebook; a map whose high entry is the wire string asks high; a null entry takes the default; the model's row over a row of every model; an unknown tag and input left over are refused
law model_facts_ffi_example:
  {FMF.ffi("0,1,F") == "F" : String} &
  {FMF.ffi("0,0,1,F") == "T" : String} &
  {FMF.ffi("1,1,F0,1,") == "F" : String} &
  {FMF.ffi("2,0,0,0,1,1,0,0,0,3,") == "0," : String} &
  {FMF.ffi("2,0,0,1,0,0,0,0,2,") == "3," : String} &
  {FMF.ffi("3,2,0,0,0,1,0,0,1,0,0,") == "1,1," : String} &
  {FMF.ffi("4,") == SCon{'E', SCon{' ', "model facts: malformed request"}} : String} &
  {FMF.ffi("0,1,Fx") == SCon{'E', SCon{' ', "model facts: malformed request"}} : String}

# LAW model_facts_ffi_reasoning_example: anchor: the bytes Rust sends and reads for the Bedrock reasoning fields: Claude sends the thinking block; GPT at max with no entry the nested max, at high with the map's string the nested code 0; no shape sends the thinking block; a shape past GPT is refused
# EXCLUDES: a codec that reads the shape, entry and level in another order
#   than Rust writes them, or replies in another form than Rust reads
law model_facts_ffi_reasoning_example:
  {FMF.ffi("4,1,0,3,") == "1," : String} &
  {FMF.ffi("4,2,0,5,") == "2,6," : String} &
  {FMF.ffi("4,2,1,1,0,3,") == "2,0," : String} &
  {FMF.ffi("4,0,1,0,0,") == "1," : String} &
  {FMF.ffi("4,3,0,0,") == SCon{'E', SCon{' ', "model facts: malformed request"}} : String}
