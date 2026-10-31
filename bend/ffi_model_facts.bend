import Base
import ./wire.bend as W
import ./infer.bend as If
import ./facts.bend as Fx

# ffi_model_facts: the model facts a wire API decides from the rulebook's
# answers (bend/facts.bend sections 1, 3 and 4: `flag`, `adaptive`,
# `effort`, `price`) as an entry of the compiled
# Bend core. Rust gathers the facts (the
# rulebook's answer for a directive, the model's compat flag, the
# AWS_BEDROCK_FORCE_CACHE flag, the thinking-level map, the price rows of
# the model's provider and API); the model decides. The texts stay in Rust: a map's wire string is sent as
# the code 0 (the defaults are 2 low, 3 medium, 4 high, so a reply 0 means
# the map's own string), a price row names this model 0 or another model 1,
# this tier 0 or another tier 1, and carries its index as its multiplier
# (the reply is the index of the row that prices the tier). Request: a tag,
# then
#   0  a flag (`Fx.flag`): the rulebook's answer (0 known, then the value:
#      1 true, any other false | 1 unknown), then the decision when no
#      rule applies (a Bool)
#   1  adaptive thinking (`Fx.adaptive`): the model's compat flag (0 none
#      | 1 then the Bool), then the rulebook's answer
#   2  the Bedrock effort (`Fx.effort`): the thinking-level map's entries,
#      minimal to max (each 0 missing | 1 then 0 null | 1 then the wire
#      code), then the level (0 minimal .. 5 max)
#   3  a service tier's multiplier (`Fx.price`): the rows (a count, then
#      each row: its model (0 every model | 1 then the model's number),
#      its tier's number and its multiplier in hundredths), then the
#      model's number and the tier's number
# Reply to 0 and 1: the Bool; to 2: the Nat; to 3: 0 no row | 1 then the
# multiplier. Any other input: the error form.

# A request of the entry
type Req is Data:
  QFlag{a: If.Ans, d: Bool}
  QAdaptive{c: Maybe<&2, Bool>, a: If.Ans}
  QEffort{m: Fx.EMap, l: Fx.ELv}
  QPrice{rows: List<&2, Fx.PRow>, m: Nat, t: Nat}

# Decoding
# --------

# a Maybe<Nat>: 0 none | 1 then the Nat
def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mnat.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_mnat(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_mnat.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the rulebook's answer: 0 known, then the value | 1 unknown
def get_ans.known(r: W.Dec<Nat>) -> W.Dec<If.Ans>:
  match r:
    case W.Got{v, s}:
      W.Got{If.Known{v}, s}
    case W.Bad{}:
      W.Bad{}

def get_ans.tag(t: Nat, s: String) -> W.Dec<If.Ans>:
  match t:
    case 0n:
      get_ans.known(W.get_nat(s))
    case 1n:
      W.Got{If.Unknown{}, s}
    case 2n+p:
      W.Bad{}

def get_ans(r: W.Dec<Nat>) -> W.Dec<If.Ans>:
  match r:
    case W.Got{t, s}:
      get_ans.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a compat flag: 0 none | 1 then the Bool
def get_mbool.some(r: W.Dec<Bool>) -> W.Dec<Maybe<&2, Bool>>:
  match r:
    case W.Got{b, s}:
      W.Got{Some{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_mbool.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Bool>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mbool.some(W.get_bool(s))
    case 2n+p:
      W.Bad{}

def get_mbool(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Bool>>:
  match r:
    case W.Got{t, s}:
      get_mbool.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a thinking-level map entry: 0 missing | 1 then 0 null | 1 then the code
def get_ent.val(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match r:
    case W.Got{v, s}:
      W.Got{Some{Some{v}}, s}
    case W.Bad{}:
      W.Bad{}

def get_ent.in(t: Nat, s: String) -> W.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match t:
    case 0n:
      W.Got{Some{None{}}, s}
    case 1n:
      get_ent.val(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_ent.inner(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match r:
    case W.Got{t, s}:
      get_ent.in(t, s)
    case W.Bad{}:
      W.Bad{}

def get_ent.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_ent.inner(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_ent(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Maybe<&2, Nat>>>:
  match r:
    case W.Got{t, s}:
      get_ent.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a request's level: 0 minimal .. 5 max
def get_elv.tag(t: Nat, s: String) -> W.Dec<Fx.ELv>:
  match t:
    case 0n:
      W.Got{Fx.EMinimal{}, s}
    case 1n:
      W.Got{Fx.ELow{}, s}
    case 2n:
      W.Got{Fx.EMedium{}, s}
    case 3n:
      W.Got{Fx.EHigh{}, s}
    case 4n:
      W.Got{Fx.EXhigh{}, s}
    case 5n:
      W.Got{Fx.EMax{}, s}
    case 6n+p:
      W.Bad{}

def get_elv(r: W.Dec<Nat>) -> W.Dec<Fx.ELv>:
  match r:
    case W.Got{t, s}:
      get_elv.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# 0 a flag: the answer, then the decision when no rule applies
def get_flag.d(a: If.Ans, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      W.Got{QFlag{a, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_flag(r: W.Dec<If.Ans>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      get_flag.d(a, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# 1 adaptive thinking: the compat flag, then the answer
def get_adaptive.a(c: Maybe<&2, Bool>, r: W.Dec<If.Ans>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QAdaptive{c, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_adaptive(r: W.Dec<Maybe<&2, Bool>>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_adaptive.a(c, get_ans(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# 2 the Bedrock effort: six entries, then the level
def get_effort.l(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, xh: Maybe<&2, Maybe<&2, Nat>>, mx: Maybe<&2, Maybe<&2, Nat>>, r: W.Dec<Fx.ELv>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      W.Got{QEffort{Fx.EMap{mi, lo, me, hi, xh, mx}, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_effort.mx(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, xh: Maybe<&2, Maybe<&2, Nat>>, r: W.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{mx, s}:
      get_effort.l(mi, lo, me, hi, xh, mx, get_elv(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_effort.xh(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, hi: Maybe<&2, Maybe<&2, Nat>>, r: W.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{xh, s}:
      get_effort.mx(mi, lo, me, hi, xh, get_ent(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_effort.hi(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, me: Maybe<&2, Maybe<&2, Nat>>, r: W.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{hi, s}:
      get_effort.xh(mi, lo, me, hi, get_ent(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_effort.me(mi: Maybe<&2, Maybe<&2, Nat>>, lo: Maybe<&2, Maybe<&2, Nat>>, r: W.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{me, s}:
      get_effort.hi(mi, lo, me, get_ent(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_effort.lo(mi: Maybe<&2, Maybe<&2, Nat>>, r: W.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{lo, s}:
      get_effort.me(mi, lo, get_ent(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_effort(r: W.Dec<Maybe<&2, Maybe<&2, Nat>>>) -> W.Dec<Req>:
  match r:
    case W.Got{mi, s}:
      get_effort.lo(mi, get_ent(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# a price row: its model (Maybe<Nat>), its tier, its multiplier
def get_row.k(m: Maybe<&2, Nat>, t: Nat, r: W.Dec<Nat>) -> W.Dec<Fx.PRow>:
  match r:
    case W.Got{k, s}:
      W.Got{Fx.PRow{m, t, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_row.t(m: Maybe<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Fx.PRow>:
  match r:
    case W.Got{t, s}:
      get_row.k(m, t, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_row.m(r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Fx.PRow>:
  match r:
    case W.Got{m, s}:
      get_row.t(m, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_row(s: String) -> W.Dec<Fx.PRow>:
  get_row.m(get_mnat(W.get_nat(s)))

def get_rows.cons(x: Fx.PRow, r: W.Dec<List<&2, Fx.PRow>>) -> W.Dec<List<&2, Fx.PRow>>:
  match r:
    case W.Got{xs, s}:
      W.Got{x <> xs, s}
    case W.Bad{}:
      W.Bad{}

# n more rows after the one cur answers
def get_rows.go(n: Nat, cur: W.Dec<Fx.PRow>) -> W.Dec<List<&2, Fx.PRow>>:
  match n:
    case 0n:
      match cur:
        case W.Got{x, s}:
          W.Got{[x], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+k:
      match cur:
        case W.Got{x, s}:
          get_rows.cons(x, get_rows.go(k, get_row(s)))
        case W.Bad{}:
          W.Bad{}

# the rows: a count, then each row
def get_rows.count(n: Nat, s: String) -> W.Dec<List<&2, Fx.PRow>>:
  match n:
    case 0n:
      W.Got{Nil{}, s}
    case 1n+k:
      get_rows.go(k, get_row(s))

def get_rows(r: W.Dec<Nat>) -> W.Dec<List<&2, Fx.PRow>>:
  match r:
    case W.Got{n, s}:
      get_rows.count(n, s)
    case W.Bad{}:
      W.Bad{}

# 3 a tier's multiplier: the rows, the model, the tier
def get_price.t(rows: List<&2, Fx.PRow>, m: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QPrice{rows, m, t}, s}
    case W.Bad{}:
      W.Bad{}

def get_price.m(rows: List<&2, Fx.PRow>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_price.t(rows, m, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_price(r: W.Dec<List<&2, Fx.PRow>>) -> W.Dec<Req>:
  match r:
    case W.Got{rows, s}:
      get_price.m(rows, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_flag(get_ans(W.get_nat(s)))
    case 1n:
      get_adaptive(get_mbool(W.get_nat(s)))
    case 2n:
      get_effort(get_ent(W.get_nat(s)))
    case 3n:
      get_price(get_rows(W.get_nat(s)))
    case 4n+p:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Encoding
# --------

def put_mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{k}:
      W.put_nat(1n, W.put_nat(k, ""))

# The decisions
# -------------

# the answer to a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QFlag{a, d}:
      W.put_bool(Fx.flag(a, d), "")
    case QAdaptive{c, a}:
      W.put_bool(Fx.adaptive(c, a), "")
    case QEffort{m, l}:
      W.put_nat(Fx.effort(m, l), "")
    case QPrice{rows, m, t}:
      put_mnat(Fx.price(rows, m, t))

def fail() -> String:
  W.err("model facts: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      fail()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_req(input))
