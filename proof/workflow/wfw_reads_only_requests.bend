# eukhe: the proof of LAW wfw_reads_only_requests
#
# PROOF: whatever a decoder of the entry reads is the laws' spelling of
# what it read, then its rest, and fits the wire (wc.*, tag by tag with
# the wire's exactness laws: an unknown tag is Bad; the rows by the list
# loop); each stage carries the input spelled up to its field (`pre`), so
# an answer that is no error comes from a request read whole, nothing
# left, and is the spelled reply (wc.fin with sp.answer).

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/workflow.bend as W
import ../../bend/wire.bend as Wr
import ../../laws/workflow.bend as Workflow
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/base/spell.bend as LAWireSpell
import ./wfw_answers_spelled/spell.bend as SP

# s spelled up to a field a is s spelled up to its spelling b
def wc.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Statuses and the prior
# ----------------------

def wc.Sts(s: String, d: Wr.Dec<W.Sts>) -> Type:
  match d:
    case Wr.Got{st, r}:
      {s == Workflow.wfw_spell_sts(st, r) : String}
    case Wr.Bad{}:
      Unit

def wc.sts.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wc.Sts(s, FW.get_sts.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s0, ed)
        case 4n:
          Wire.wire_nat_exact(s, 4n, s0, ed)
        case 5n:
          Wire.wire_nat_exact(s, 5n, s0, ed)
        case 6n+x:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a status decoded is spelled
def wc.sts(+s: String) -> wc.Sts(s, FW.get_sts(s)):
  wc.sts.go(s, Wr.get_nat(s), {==})

def wc.Prior(s: String, d: Wr.Dec<Maybe<&2, W.Sts>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Workflow.wfw_spell_prior(m, r) : String}
    case Wr.Bad{}:
      Unit

def wc.prior.some(-s: String, -s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<W.Sts>, xd: wc.Sts(s0, d)) -> wc.Prior(s, FW.get_prior.some(d)):
  match d:
    case Wr.Got{+st, +r}:
      wc.step(z => Wr.put_nat(1n, z), s, s0, Workflow.wfw_spell_sts(st, r), pre, xd)
    case Wr.Bad{}:
      Unit{}

def wc.prior.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wc.Prior(s, FW.get_prior.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          wc.prior.some(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FW.get_sts(s0), wc.sts(s0))
        case 2n+x:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a prior decoded is spelled
def wc.prior(+s: String) -> wc.Prior(s, FW.get_prior(s)):
  wc.prior.go(s, Wr.get_nat(s), {==})

# Rows
# ----

def wc.Row(s: String, d: Wr.Dec<W.Row>) -> Type:
  match d:
    case Wr.Got{rw, r}:
      {s == Workflow.wfw_spell_row(rw, r) : String} & {Workflow.wfw_row_fits(rw) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wc.row.sts(-s: String, +k: Nat, -s1: String, pre: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<W.Sts>, xd: wc.Sts(s1, d)) -> wc.Row(s, FW.get_row.sts(k, d)):
  match d:
    case Wr.Got{+st, +r}:
      (wc.step(z => Wr.put_nat(k, z), s, s1, Workflow.wfw_spell_sts(st, r), pre, xd), fk)
    case Wr.Bad{}:
      Unit{}

def wc.row.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wc.Row(s, FW.get_row.go(d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      wc.row.sts(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), FW.get_sts(s1), wc.sts(s1))
    case Wr.Bad{}:
      Unit{}

# a row decoded is spelled, and its key fits
def wc.row(+s: String) -> wc.Row(s, FW.get_row(s)):
  wc.row.go(s, Wr.get_nat(s), {==})

def wc.cons_fit(x: W.Row, -t: List<&2, W.Row>, fx: {Workflow.wfw_row_fits(x) == True{} : Bool}, ft: {Workflow.wfw_rows_fit(t) == True{} : Bool}) -> {Workflow.wfw_rows_fit(x <> t) == True{} : Bool}:
  LAWireSpell.ws_and_tt(Workflow.wfw_row_fits(x), Workflow.wfw_rows_fit(t), fx, ft)

# what the item loop's answer says about its input s (m + 1 rows)
def wc.PL(s: String, m: Nat, d: Wr.Dec<List<&2, W.Row>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Workflow.wfw_spell_rows.items(xs, r) : String} & ({List.length(&2, W.Row, xs) == 1n+m : Nat} & {Workflow.wfw_rows_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def wc.rows.step(-s: String, +x: W.Row, +s3: String, -k: Nat, ex: {s == Workflow.wfw_spell_row(x, s3) : String}, fx: {Workflow.wfw_row_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, W.Row>>, ih: wc.PL(s3, k, d)) -> wc.PL(s, 1n+k, Wr.get_list.cons(W.Row, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Workflow.wfw_spell_row(x, s3), Workflow.wfw_spell_row(x, Workflow.wfw_spell_rows.items(ys, r)), ex,
          Equal.cong(String, String, z => Workflow.wfw_spell_row(x, z), s3, Workflow.wfw_spell_rows.items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, W.Row, ys), 1n+k, e2), wc.cons_fit(x, ys, fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled rows that fit
def wc.rows.loop(m: Nat, cur: Wr.Dec<W.Row>, +s: String, pc: wc.Row(s, cur)) ->
  wc.PL(s, m, Wr.get_list.go(~W.Row, ~FW.get_row, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, wc.cons_fit(x, Nil{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      wc.rows.step(s, x, s3, k, e, f, Wr.get_list.go(~W.Row, ~FW.get_row, k, FW.get_row(s3)),
        wc.rows.loop(k, FW.get_row(s3), s3, wc.row(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a rows decoder's answer says about its input s
def wc.LS(s: String, d: Wr.Dec<List<&2, W.Row>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Workflow.wfw_spell_rows(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, W.Row, xs)) == True{} : Bool} & {Workflow.wfw_rows_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def wc.rows.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, W.Row>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == Workflow.wfw_spell_rows.items(xs, r) : String},
  e2: {List.length(&2, W.Row, xs) == 1n+m : Nat}) -> {s == Workflow.wfw_spell_rows(xs, r) : String}:
  %Equal.sym(Nat, List.length(&2, W.Row, xs), 1n+m, e2) : {s == Wr.put_nat(_, Workflow.wfw_spell_rows.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def wc.rows.conv_f(-m: Nat, -xs: List<&2, W.Row>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, W.Row, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, W.Row, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, W.Row, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def wc.rows.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, W.Row>>, pl: wc.PL(s2, m, d)) -> wc.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (wc.rows.conv_s(s, s2, m, xs, r, en, e1, e2), (wc.rows.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def wc.rows.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  wc.LS(s, Wr.get_list.start(~W.Row, ~FW.get_row, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      wc.rows.conv(s, s2, m, en, fn, Wr.get_list.go(~W.Row, ~FW.get_row, m, FW.get_row(s2)),
        wc.rows.loop(m, FW.get_row(s2), s2, wc.row(s2)))

def wc.rows.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  wc.LS(s, Wr.get_list.start(~W.Row, ~FW.get_row, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      wc.rows.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of rows decoded is spelled, and its count and keys fit
def wc.rows(+s: String) -> wc.LS(s, Wr.get_list(~W.Row, ~FW.get_row, s)):
  wc.rows.top(s, Wr.get_nat(s), {==})

# The pool
# --------

def wc.Pool(s: String, d: Wr.Dec<W.Pool>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == Workflow.wfw_spell_pool(p, r) : String} & {Workflow.wfw_pool_fits(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wc.pool.left(-s: String, +t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wc.Pool(s, FW.get_pool.left(t, d)):
  match d:
    case Wr.Got{+l, +s2}:
      +e = ed
      (wc.step(z => Wr.put_nat(t, z), s, s1, Wr.put_nat(l, s2), pre, Wire.wire_nat_exact(s1, l, s2, e)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(t), LawsBase.wire_fits(l), ft, Wire.wire_nat_decoded_fits(s1, l, s2, e)))
    case Wr.Bad{}:
      Unit{}

def wc.pool.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wc.Pool(s, FW.get_pool.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      +e = ed
      wc.pool.left(s, t, s1, Wire.wire_nat_exact(s, t, s1, e), Wire.wire_nat_decoded_fits(s, t, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a pool decoded is spelled, and fits
def wc.pool(+s: String) -> wc.Pool(s, FW.get_pool(s)):
  wc.pool.go(s, Wr.get_nat(s), {==})

# The request
# -----------

def wc.Req(s: String, d: Wr.Dec<FW.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Workflow.wfw_spell_req(q, r) : String} & {Workflow.wfw_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wc.req.pool(-s: String, +m: Maybe<&2, W.Sts>, +k: Nat, +rows: List<&2, W.Row>, -s3: String,
  pre: {s == Wr.put_nat(0n, Workflow.wfw_spell_prior(m, Wr.put_nat(k, Workflow.wfw_spell_rows(rows, s3)))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool}, fl: {LawsBase.wire_fits(List.length(&2, W.Row, rows)) == True{} : Bool},
  fr: {Workflow.wfw_rows_fit(rows) == True{} : Bool}, d: Wr.Dec<W.Pool>, xd: wc.Pool(s3, d)) -> wc.Req(s, FW.get_req.pool(m, k, rows, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, fp) = xd
      +lt = Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, rows)), Workflow.wfw_rows_fit(rows))
      (wc.step(z => Wr.put_nat(0n, Workflow.wfw_spell_prior(m, Wr.put_nat(k, Workflow.wfw_spell_rows(rows, z)))), s, s3, Workflow.wfw_spell_pool(p, r), pre, e),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), Bool.and(lt, Workflow.wfw_pool_fits(p)), fk,
          LAWireSpell.ws_and_tt(lt, Workflow.wfw_pool_fits(p), LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, W.Row, rows)), Workflow.wfw_rows_fit(rows), fl, fr), fp)))
    case Wr.Bad{}:
      Unit{}

def wc.req.rows(-s: String, +m: Maybe<&2, W.Sts>, +k: Nat, -s2: String,
  pre: {s == Wr.put_nat(0n, Workflow.wfw_spell_prior(m, Wr.put_nat(k, s2))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, W.Row>>, xd: wc.LS(s2, d)) -> wc.Req(s, FW.get_req.rows(m, k, d)):
  match d:
    case Wr.Got{+rows, +s3}:
      (e, f) = xd
      (fl, fr) = f
      wc.req.pool(s, m, k, rows, s3, wc.step(z => Wr.put_nat(0n, Workflow.wfw_spell_prior(m, Wr.put_nat(k, z))), s, s2, Workflow.wfw_spell_rows(rows, s3), pre, e), fk, fl, fr, FW.get_pool(s3), wc.pool(s3))
    case Wr.Bad{}:
      Unit{}

def wc.req.key(-s: String, +m: Maybe<&2, W.Sts>, +s1: String, pre: {s == Wr.put_nat(0n, Workflow.wfw_spell_prior(m, s1)) : String},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wc.Req(s, FW.get_req.key(m, d)):
  match d:
    case Wr.Got{+k, +s2}:
      +e = ed
      wc.req.rows(s, m, k, s2, wc.step(z => Wr.put_nat(0n, Workflow.wfw_spell_prior(m, z)), s, s1, Wr.put_nat(k, s2), pre, Wire.wire_nat_exact(s1, k, s2, e)), Wire.wire_nat_decoded_fits(s1, k, s2, e), Wr.get_list(~W.Row, ~FW.get_row, s2), wc.rows(s2))
    case Wr.Bad{}:
      Unit{}

def wc.req.admit(-s: String, -s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Maybe<&2, W.Sts>>, xd: wc.Prior(s0, d)) -> wc.Req(s, FW.get_req.admit(d)):
  match d:
    case Wr.Got{+m, +s1}:
      wc.req.key(s, m, s1, wc.step(z => Wr.put_nat(0n, z), s, s0, Workflow.wfw_spell_prior(m, s1), pre, xd), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def wc.req.cap(-s: String, +c: Nat, +mx: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(mx, s2))) : String},
  fc: {LawsBase.wire_fits(c) == True{} : Bool}, fm: {LawsBase.wire_fits(mx) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> wc.Req(s, FW.get_req.cap(c, mx, d)):
  match d:
    case Wr.Got{+cap, +s3}:
      +e = ed
      (wc.step(z => Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(mx, z))), s, s2, Wr.put_nat(cap, s3), pre, Wire.wire_nat_exact(s2, cap, s3, e)),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(mx), LawsBase.wire_fits(cap)), fc,
          LAWireSpell.ws_and_tt(LawsBase.wire_fits(mx), LawsBase.wire_fits(cap), fm, Wire.wire_nat_decoded_fits(s2, cap, s3, e))))
    case Wr.Bad{}:
      Unit{}

def wc.req.max(-s: String, +c: Nat, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(c, s1)) : String},
  fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wc.Req(s, FW.get_req.max(c, d)):
  match d:
    case Wr.Got{+mx, +s2}:
      +e = ed
      wc.req.cap(s, c, mx, s2, wc.step(z => Wr.put_nat(1n, Wr.put_nat(c, z)), s, s1, Wr.put_nat(mx, s2), pre, Wire.wire_nat_exact(s1, mx, s2, e)), fc, Wire.wire_nat_decoded_fits(s1, mx, s2, e), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def wc.req.limits(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> wc.Req(s, FW.get_req.limits(d)):
  match d:
    case Wr.Got{+c, +s1}:
      +e = ed
      wc.req.max(s, c, s1, wc.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(c, s1), pre, Wire.wire_nat_exact(s0, c, s1, e)), Wire.wire_nat_decoded_fits(s0, c, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def wc.req.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wc.Req(s, FW.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          wc.req.admit(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FW.get_prior(s0), wc.prior(s0))
        case 1n:
          wc.req.limits(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+x:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def wc.req(+s: String) -> wc.Req(s, FW.get_req(s)):
  wc.req.go(s, Wr.get_nat(s), {==})

# The entry
# ---------

def wc.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FW.Req, q => {(s, (Workflow.wfw_req_fits(q), a)) == (Workflow.wfw_spell_req(q, ""), (True{}, Workflow.wfw_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def wc.top_eq(+s: String, +q: FW.Req, +a: String, e: {s == Workflow.wfw_spell_req(q, "") : String}, f: {Workflow.wfw_req_fits(q) == True{} : Bool}, ea: {a == Workflow.wfw_spell_answer(q) : String}) -> {(s, (Workflow.wfw_req_fits(q), a)) == (Workflow.wfw_spell_req(q, ""), (True{}, Workflow.wfw_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, Workflow.wfw_spell_req(q, ""), e) : {(_, (Workflow.wfw_req_fits(q), a)) == (Workflow.wfw_spell_req(q, ""), (True{}, Workflow.wfw_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Workflow.wfw_req_fits(q), True{}, f) : {(Workflow.wfw_spell_req(q, ""), (_, a)) == (Workflow.wfw_spell_req(q, ""), (True{}, Workflow.wfw_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, Workflow.wfw_spell_answer(q), ea) : {(Workflow.wfw_spell_req(q, ""), (True{}, _)) == (Workflow.wfw_spell_req(q, ""), (True{}, Workflow.wfw_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def wc.fin(+s: String, +q: FW.Req, r: String, pre: {s == Workflow.wfw_spell_req(q, r) : String}, f: {Workflow.wfw_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FW.ffi.end(Wr.end(r), q)) == False{} : Bool}) -> wc.G(s, FW.ffi.end(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, wc.top_eq(s, q, FW.ffi.end(True{}, q), pre, f, SP.sp.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(wc.G(s, FW.ffi.end(False{}, q)), ok)

def wc.main(+s: String, d: Wr.Dec<FW.Req>, inv: wc.Req(s, d), ok: {LawsBase.wire_opens_err(FW.ffi.go(d)) == False{} : Bool}) -> wc.G(s, FW.ffi.go(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      wc.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(wc.G(s, Wr.err("workflow: malformed request")), ok)

def Workflow.wfw_reads_only_requests(s, ok):
  wc.main(s, FW.get_req(s), wc.req(s), ok)
