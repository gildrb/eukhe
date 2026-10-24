# eukhe: the laws of area model_facts

import Base
import ../bend/facts.bend as Fx
import ../bend/ffi_model_facts.bend as FMF
import ../bend/infer.bend as If
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- model_facts ----

# (S6.10) The entry of the model facts: bend/ffi_model_facts.bend
# (laws/facts.bend pins the model terms it calls: facts_flag_exact,
# facts_effort_exact, facts_price_exact)
# ----------------------------------------------------------------
# Rust gathers the rulebook's answers, the compat flag, the env flag, the
# thinking-level map (a wire string as the code 0) and the price rows of
# the model's provider and API (this model 0, another 1; this tier 0,
# another 1; the row's index as its multiplier); the model decides. The
# spellers write what Rust writes with the wire primitives only.

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

# Reader: the requests the entry accepts, read with the wire primitives

# a Maybe<Nat>: 0 none | 1 then the Nat
def mfr.get_mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_mnat.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      mfr.get_mnat.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def mfr.get_mnat(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_mnat.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the rulebook's answer: 0 known, then the value | 1 unknown
def mfr.get_ans.known(r: Wr.Dec<Nat>) -> Wr.Dec<If.Ans>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{If.Known{v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_ans.tag(t: Nat, s: String) -> Wr.Dec<If.Ans>:
  match t:
    case 0n:
      mfr.get_ans.known(Wr.get_nat(s))
    case 1n:
      Wr.Got{If.Unknown{}, s}
    case 2n+p:
      Wr.Bad{}

def mfr.get_ans(r: Wr.Dec<Nat>) -> Wr.Dec<If.Ans>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_ans.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a compat flag: 0 none | 1 then the Bool
def mfr.get_mbool.some(r: Wr.Dec<Bool>) -> Wr.Dec<Maybe<&2, Bool>>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{Some{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_mbool.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Bool>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      mfr.get_mbool.some(Wr.get_bool(s))
    case 2n+p:
      Wr.Bad{}

def mfr.get_mbool(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Bool>>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_mbool.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a thinking-level map entry: 0 missing | 1 then 0 null | 1 then the code
def mfr.get_ent.val(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{Some{Some{v}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_ent.in(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match t:
    case 0n:
      Wr.Got{Some{None{}}, s}
    case 1n:
      mfr.get_ent.val(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def mfr.get_ent.inner(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_ent.in(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_ent.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      mfr.get_ent.inner(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def mfr.get_ent(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_ent.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a request's level: 0 minimal .. 5 max
def mfr.get_elv.tag(t: Nat, s: String) -> Wr.Dec<Fx.ELv>:
  match t:
    case 0n:
      Wr.Got{Fx.EMinimal{}, s}
    case 1n:
      Wr.Got{Fx.ELow{}, s}
    case 2n:
      Wr.Got{Fx.EMedium{}, s}
    case 3n:
      Wr.Got{Fx.EHigh{}, s}
    case 4n:
      Wr.Got{Fx.EXhigh{}, s}
    case 5n:
      Wr.Got{Fx.EMax{}, s}
    case 6n+p:
      Wr.Bad{}

def mfr.get_elv(r: Wr.Dec<Nat>) -> Wr.Dec<Fx.ELv>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_elv.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# 0 a flag: the answer, then the decision when no rule applies
def mfr.get_flag.d(a: If.Ans, r: Wr.Dec<Bool>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{FMF.QFlag{a, d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_flag(r: Wr.Dec<If.Ans>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{a, s}:
      mfr.get_flag.d(a, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

# 1 adaptive thinking: the compat flag, then the answer
def mfr.get_adaptive.a(c: Maybe<&2, Bool>, r: Wr.Dec<If.Ans>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{FMF.QAdaptive{c, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_adaptive(r: Wr.Dec<Maybe<&2, Bool>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{c, s}:
      mfr.get_adaptive.a(c, mfr.get_ans(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# 2 the Bedrock effort: six entries, then the level
def mfr.get_effort.l(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, xh: Maybe<&2, Maybe<&2, Nat>>, mx: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Fx.ELv>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{FMF.QEffort{Fx.EMap{mi, lo, me, hi, xh, mx}, l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_effort.mx(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, xh: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{mx, s}:
      mfr.get_effort.l(mi, lo, me, hi, xh, mx, mfr.get_elv(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_effort.xh(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{xh, s}:
      mfr.get_effort.mx(mi, lo, me, hi, xh, mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_effort.hi(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{hi, s}:
      mfr.get_effort.xh(mi, lo, me, hi, mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_effort.me(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{me, s}:
      mfr.get_effort.hi(mi, lo, me, mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_effort.lo(mi: Maybe<&2, Maybe<&2, Nat>>, r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{lo, s}:
      mfr.get_effort.me(mi, lo, mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_effort(r: Wr.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{mi, s}:
      mfr.get_effort.lo(mi, mfr.get_ent(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a price row: its model (Maybe<Nat>), its tier, its multiplier
def mfr.get_row.k(m: Maybe<&2, Nat>, t: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.PRow>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{Fx.PRow{m, t, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_row.t(m: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<Fx.PRow>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_row.k(m, t, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_row.m(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Fx.PRow>:
  match r:
    case Wr.Got{m, s}:
      mfr.get_row.t(m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_row(s: String) -> Wr.Dec<Fx.PRow>:
  mfr.get_row.m(mfr.get_mnat(Wr.get_nat(s)))

def mfr.get_rows.cons(x: Fx.PRow, r: Wr.Dec<List<&2, Fx.PRow>>) -> Wr.Dec<List<&2, Fx.PRow>>:
  match r:
    case Wr.Got{xs, s}:
      Wr.Got{x <> xs, s}
    case Wr.Bad{}:
      Wr.Bad{}

# n more rows after the one cur answers
def mfr.get_rows.go(n: Nat, cur: Wr.Dec<Fx.PRow>) -> Wr.Dec<List<&2, Fx.PRow>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          Wr.Got{[x], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+k:
      match cur:
        case Wr.Got{x, s}:
          mfr.get_rows.cons(x, mfr.get_rows.go(k, mfr.get_row(s)))
        case Wr.Bad{}:
          Wr.Bad{}

# the rows: a count, then each row
def mfr.get_rows.count(n: Nat, s: String) -> Wr.Dec<List<&2, Fx.PRow>>:
  match n:
    case 0n:
      Wr.Got{Nil{}, s}
    case 1n+k:
      mfr.get_rows.go(k, mfr.get_row(s))

def mfr.get_rows(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, Fx.PRow>>:
  match r:
    case Wr.Got{n, s}:
      mfr.get_rows.count(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

# 3 a tier's multiplier: the rows, the model, the tier
def mfr.get_price.t(rows: List<&2, Fx.PRow>, m: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{FMF.QPrice{rows, m, t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_price.m(rows: List<&2, Fx.PRow>, r: Wr.Dec<Nat>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{m, s}:
      mfr.get_price.t(rows, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_price(r: Wr.Dec<List<&2, Fx.PRow>>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{rows, s}:
      mfr.get_price.m(rows, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def mfr.get_req.tag(t: Nat, s: String) -> Wr.Dec<FMF.Req>:
  match t:
    case 0n:
      mfr.get_flag(mfr.get_ans(Wr.get_nat(s)))
    case 1n:
      mfr.get_adaptive(mfr.get_mbool(Wr.get_nat(s)))
    case 2n:
      mfr.get_effort(mfr.get_ent(Wr.get_nat(s)))
    case 3n:
      mfr.get_price(mfr.get_rows(Wr.get_nat(s)))
    case 4n+p:
      Wr.Bad{}

def mfr.get_req.go(r: Wr.Dec<Nat>) -> Wr.Dec<FMF.Req>:
  match r:
    case Wr.Got{t, s}:
      mfr.get_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the start of s
def mfr.get_req(s: String) -> Wr.Dec<FMF.Req>:
  mfr.get_req.go(Wr.get_nat(s))

def mfr.end(whole: Bool, q: FMF.Req) -> Maybe<&2, FMF.Req>:
  match whole:
    case True{}:
      Some{q}
    case False{}:
      None{}

def mfr.whole(r: Wr.Dec<FMF.Req>) -> Maybe<&2, FMF.Req>:
  match r:
    case Wr.Got{q, s}:
      mfr.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def mfr.read(s: String) -> Maybe<&2, FMF.Req>:
  mfr.whole(mfr.get_req(s))

# LAW model_facts_ffi_flag: a flag request answers the model's flag decision
law model_facts_ffi_flag:
  for +a: If.Ans
  for +d: Bool
  for fits: {mf.ans_fits(a) == True{} : Bool}
  {FMF.ffi(spell_flag(a, d)) == Wr.put_bool(Fx.flag(a, d), "") : String}

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

# LAW model_facts_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "model facts: malformed request"
law model_facts_ffi_malformed_exact:
  for +s: String
  for no: {mfr.read(s) == None{} : Maybe<&2, FMF.Req>}
  {FMF.ffi(s) == SCon{'E', SCon{' ', "model facts: malformed request"}} : String}

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
