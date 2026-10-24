# eukhe: shared lemmas of the doc_tags proofs (F3, grep's tags)
#
# The scan codec of bend/ffi_doc_tags.bend against the spec's spelling
# (laws/doc_tags.bend sp_w_scan, sp_w_req), both directions: a spelled
# scan or request reads back (ptg.scan_rt, ptg.go_rt), and a decoder
# answers Got only for a spelled input (ptg.scan, ptg.req). The reply's
# encoder equals the spec's (ptg.reply).

import Base
import ../../bend/doc_tags.bend as Dt
import ../../bend/ffi_doc_tags.bend as FDt
import ../../bend/wire.bend as Wr
import ../../laws/doc_tags.bend as DocTags
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire

# Logic
# -----

def ptg.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def ptg.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : ptg.BT(_, G)
  Unit{}

# Fates
# -----

def ptg.fate(s: Dt.Scan) -> {Dt.fate(s) == DocTags.sp_fate(s) : Dt.Fate}:
  match s:
    case Dt.Part{}:
      {==}
    case Dt.Whole{u}:
      match u:
        case True{}:
          {==}
        case False{}:
          {==}

def ptg.fates(+ss: List<&2, Dt.Scan>) -> {Dt.fates(ss) == DocTags.sp_fates(ss) : List<&2, Dt.Fate>}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      %Equal.sym(Dt.Fate, Dt.fate(s), DocTags.sp_fate(s), ptg.fate(s)) : {_ <> Dt.fates(t) == DocTags.sp_fate(s) <> DocTags.sp_fates(t) : List<&2, Dt.Fate>}
      %Equal.sym(List<&2, Dt.Fate>, Dt.fates(t), DocTags.sp_fates(t), ptg.fates(t)) : {DocTags.sp_fate(s) <> _ == DocTags.sp_fate(s) <> DocTags.sp_fates(t) : List<&2, Dt.Fate>}
      {==}

# Reply
# -----

# the spec's items of a list of fates, then rest
def ptg.fitems(xs: List<&2, Dt.Fate>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocTags.sp_w_fate(x, ptg.fitems(t, rest))

# one step of the entry's reply encoder is the spec's
def ptg.fput_step(x: Dt.Fate, -n: Nat, -r: String) -> {Wr.put_list.step(~Dt.Fate, ~FDt.put_fate, x, (n, r)) == (1n+n, DocTags.sp_w_fate(x, r)) : Nat & String}:
  match x:
    case Dt.Tagged{}:
      {==}
    case Dt.OverLimit{}:
      {==}
    case Dt.NotUtf8{}:
      {==}

def ptg.fput_go(xs: List<&2, Dt.Fate>, -rest: String) ->
  {Wr.put_list.go(~Dt.Fate, ~FDt.put_fate, xs, rest) == (List.length(&2, Dt.Fate, xs), ptg.fitems(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dt.Fate, ~FDt.put_fate, t, rest), (List.length(&2, Dt.Fate, t), ptg.fitems(t, rest)), ptg.fput_go(t, rest)) : {Wr.put_list.step(~Dt.Fate, ~FDt.put_fate, x, _) == (1n+List.length(&2, Dt.Fate, t), DocTags.sp_w_fate(x, ptg.fitems(t, rest))) : Nat & String}
      ptg.fput_step(x, List.length(&2, Dt.Fate, t), ptg.fitems(t, rest))

def ptg.sput_go(xs: List<&2, Dt.Fate>, -rest: String) ->
  {Wr.put_list.go(~Dt.Fate, ~DocTags.sp_w_fate, xs, rest) == (List.length(&2, Dt.Fate, xs), ptg.fitems(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dt.Fate, ~DocTags.sp_w_fate, t, rest), (List.length(&2, Dt.Fate, t), ptg.fitems(t, rest)), ptg.sput_go(t, rest)) : {Wr.put_list.step(~Dt.Fate, ~DocTags.sp_w_fate, x, _) == (1n+List.length(&2, Dt.Fate, t), DocTags.sp_w_fate(x, ptg.fitems(t, rest))) : Nat & String}
      {==}

# the entry's reply encoder is the spec's
def ptg.reply(+xs: List<&2, Dt.Fate>, -rest: String) ->
  {Wr.put_list(~Dt.Fate, ~FDt.put_fate, xs, rest) == Wr.put_list(~Dt.Fate, ~DocTags.sp_w_fate, xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dt.Fate, ~FDt.put_fate, xs, rest), (List.length(&2, Dt.Fate, xs), ptg.fitems(xs, rest)), ptg.fput_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_list(~Dt.Fate, ~DocTags.sp_w_fate, xs, rest) : String}
  %Equal.sym(Nat & String, Wr.put_list.go(~Dt.Fate, ~DocTags.sp_w_fate, xs, rest), (List.length(&2, Dt.Fate, xs), ptg.fitems(xs, rest)), ptg.sput_go(xs, rest)) : {Wr.put_list.fin((List.length(&2, Dt.Fate, xs), ptg.fitems(xs, rest))) == Wr.put_list.fin(_) : String}
  {==}

# the entry's reply is a count, then the items: never the error form
def ptg.reply_not_err(+xs: List<&2, Dt.Fate>, +rest: String) -> {LawsBase.wire_opens_err(Wr.put_list(~Dt.Fate, ~FDt.put_fate, xs, rest)) == False{} : Bool}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dt.Fate, ~FDt.put_fate, xs, rest), (List.length(&2, Dt.Fate, xs), ptg.fitems(xs, rest)), ptg.fput_go(xs, rest)) : {LawsBase.wire_opens_err(Wr.put_list.fin(_)) == False{} : Bool}
  Wire.wire_nat_not_err(List.length(&2, Dt.Fate, xs), ptg.fitems(xs, rest))

# Request: spelled requests read back
# -----------------------------------

# the spec's items of a list of scans, then rest
def ptg.items(xs: List<&2, Dt.Scan>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocTags.sp_w_scan(x, ptg.items(t, rest))

def ptg.put_go(xs: List<&2, Dt.Scan>, -rest: String) ->
  {Wr.put_list.go(~Dt.Scan, ~DocTags.sp_w_scan, xs, rest) == (List.length(&2, Dt.Scan, xs), ptg.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dt.Scan, ~DocTags.sp_w_scan, t, rest), (List.length(&2, Dt.Scan, t), ptg.items(t, rest)), ptg.put_go(t, rest)) : {Wr.put_list.step(~Dt.Scan, ~DocTags.sp_w_scan, x, _) == (1n+List.length(&2, Dt.Scan, t), DocTags.sp_w_scan(x, ptg.items(t, rest))) : Nat & String}
      {==}

# a request is its count, then its items
def ptg.put(+xs: List<&2, Dt.Scan>, -rest: String) ->
  {DocTags.sp_w_req(xs, rest) == Wr.put_nat(List.length(&2, Dt.Scan, xs), ptg.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dt.Scan, ~DocTags.sp_w_scan, xs, rest), (List.length(&2, Dt.Scan, xs), ptg.items(xs, rest)), ptg.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dt.Scan, xs), ptg.items(xs, rest)) : String}
  {==}

# a spelled scan reads back
def ptg.scan_rt(x: Dt.Scan, +rest: String) -> {FDt.get_scan(DocTags.sp_w_scan(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dt.Scan>}:
  match x:
    case Dt.Part{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {FDt.get_scan.start(_) == Wr.Got{Dt.Part{}, rest} : Wr.Dec<Dt.Scan>}
      {==}
    case Dt.Whole{+u}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_bool(u, rest))), Wr.Got{1n, Wr.put_bool(u, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_bool(u, rest), {==})) : {FDt.get_scan.start(_) == Wr.Got{Dt.Whole{u}, rest} : Wr.Dec<Dt.Scan>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(u, rest)), Wr.Got{u, rest}, Wire.wire_bool_round_trip(u, rest)) : {FDt.get_scan.whole(_) == Wr.Got{Dt.Whole{u}, rest} : Wr.Dec<Dt.Scan>}
      {==}

# the item loop reads back x then t
def ptg.go_rt(+t: List<&2, Dt.Scan>, +x: Dt.Scan, +rest: String) ->
  {Wr.get_list.go(~Dt.Scan, ~FDt.get_scan, List.length(&2, Dt.Scan, t), FDt.get_scan(DocTags.sp_w_scan(x, ptg.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dt.Scan>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dt.Scan>, FDt.get_scan(DocTags.sp_w_scan(x, rest)), Wr.Got{x, rest}, ptg.scan_rt(x, rest)) : {Wr.get_list.go(~Dt.Scan, ~FDt.get_scan, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dt.Scan>>}
      {==}
    case Con{+y, +u}:
      +r2 = DocTags.sp_w_scan(y, ptg.items(u, rest))
      %Equal.sym(Wr.Dec<Dt.Scan>, FDt.get_scan(DocTags.sp_w_scan(x, r2)), Wr.Got{x, r2}, ptg.scan_rt(x, r2)) : {Wr.get_list.go(~Dt.Scan, ~FDt.get_scan, 1n+List.length(&2, Dt.Scan, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dt.Scan>>}
      %Equal.sym(Wr.Dec<List<&2, Dt.Scan>>, Wr.get_list.go(~Dt.Scan, ~FDt.get_scan, List.length(&2, Dt.Scan, u), FDt.get_scan(r2)), Wr.Got{y <> u, rest}, ptg.go_rt(u, y, rest)) : {Wr.get_list.cons(Dt.Scan, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dt.Scan>>}
      {==}

# Request: only spelled requests decode
# -------------------------------------

# what a scan decoder answer says about its input s
def ptg.SP(s: String, d: Wr.Dec<Dt.Scan>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == DocTags.sp_w_scan(x, r) : String}
    case Wr.Bad{}:
      Unit

def ptg.whole(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> ptg.SP(s, FDt.get_scan.whole(d)):
  match d:
    case Wr.Got{+u, +s2}:
      Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_bool(u, s2)), pre,
        Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_bool(u, s2), Wire.wire_bool_exact(s1, u, s2, ed)))
    case Wr.Bad{}:
      Unit{}

def ptg.tag(-s: String, t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> ptg.SP(s, FDt.get_scan.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n+a:
      match a:
        case 0n:
          ptg.whole(s, s1, pre, Wr.get_bool(s1), {==})
        case 1n+b:
          Unit{}

def ptg.start(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ptg.SP(s, FDt.get_scan.start(d)):
  match d:
    case Wr.Got{+t, +s1}:
      ptg.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a scan decoded is spelled
def ptg.scan(+s: String) -> ptg.SP(s, FDt.get_scan(s)):
  ptg.start(s, Wr.get_nat(s), {==})

# what the item loop's answer says about its input s (m + 1 items)
def ptg.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Dt.Scan>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ptg.items(xs, r) : String} & {List.length(&2, Dt.Scan, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def ptg.step(-s: String, +x: Dt.Scan, +s3: String, -k: Nat, ex: {s == DocTags.sp_w_scan(x, s3) : String},
  d: Wr.Dec<List<&2, Dt.Scan>>, ih: ptg.PL(s3, k, d)) -> ptg.PL(s, 1n+k, Wr.get_list.cons(Dt.Scan, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, DocTags.sp_w_scan(x, s3), DocTags.sp_w_scan(x, ptg.items(ys, r)), ex,
          Equal.cong(String, String, z => DocTags.sp_w_scan(x, z), s3, ptg.items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dt.Scan, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items
def ptg.loop(m: Nat, cur: Wr.Dec<Dt.Scan>, +s: String, pc: ptg.SP(s, cur)) ->
  ptg.PL(s, m, Wr.get_list.go(~Dt.Scan, ~FDt.get_scan, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ptg.step(s, x, s3, k, pc, Wr.get_list.go(~Dt.Scan, ~FDt.get_scan, k, FDt.get_scan(s3)),
        ptg.loop(k, FDt.get_scan(s3), s3, ptg.scan(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a request decoder answer says about its input s
def ptg.LS(s: String, d: Wr.Dec<List<&2, Dt.Scan>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == DocTags.sp_w_req(xs, r) : String} & {DocTags.sp_fit_req(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ptg.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Dt.Scan>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == ptg.items(xs, r) : String},
  e2: {List.length(&2, Dt.Scan, xs) == 1n+m : Nat}) -> {s == DocTags.sp_w_req(xs, r) : String}:
  %Equal.sym(String, DocTags.sp_w_req(xs, r), Wr.put_nat(List.length(&2, Dt.Scan, xs), ptg.items(xs, r)), ptg.put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Dt.Scan, xs), 1n+m, e2) : {s == Wr.put_nat(_, ptg.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def ptg.conv_f(-m: Nat, -xs: List<&2, Dt.Scan>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, Dt.Scan, xs) == 1n+m : Nat}) -> {DocTags.sp_fit_req(xs) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Dt.Scan, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def ptg.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Dt.Scan>>, pl: ptg.PL(s2, m, d)) -> ptg.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = pl
      (ptg.conv_s(s, s2, m, xs, r, en, e1, e2), ptg.conv_f(m, xs, fn, e2))
    case Wr.Bad{}:
      Unit{}

def ptg.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  ptg.LS(s, Wr.get_list.start(~Dt.Scan, ~FDt.get_scan, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, fn)
    case 1n++m:
      ptg.conv(s, s2, m, en, fn, Wr.get_list.go(~Dt.Scan, ~FDt.get_scan, m, FDt.get_scan(s2)),
        ptg.loop(m, FDt.get_scan(s2), s2, ptg.scan(s2)))

def ptg.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  ptg.LS(s, Wr.get_list.start(~Dt.Scan, ~FDt.get_scan, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      ptg.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and its count fits
def ptg.req(+s: String) -> ptg.LS(s, FDt.get_req(s)):
  ptg.top(s, Wr.get_nat(s), {==})
