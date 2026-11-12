# eukhe: lemmas of the entry proofs of area budget_share
# (bend/ffi_budget_share.bend): a spelled request that fits reads back
# (bse.reads: each field by the round trips of the budget entry's
# decoders, proof/budget/base/entry.bend), and the decoder answers a
# request only for an input that is its spelling, every number and count
# within the wire (bsx.*: a predicate per decoder answer, carried stage by
# stage with wire_nat_exact, wire_nat_decoded_fits and the generic list
# laws)

import Base
import ../../../bend/budget.bend as B
import ../../../bend/ffi_budget.bend as FBg
import ../../../bend/ffi_budget_share.bend as FBs
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/budget.bend as Budget
import ../../../laws/budget_share.bend as BudgetShare
import ../../budget/base/entry.bend as BE
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../../wire/wire_list_spells_items.bend as PWireListSpellsItems
import ../../wire/base/dec.bend as LAWireDec
import ../../base/bool.bend as LBool

# Round trip
# ----------

# the tag of a use is read as that use
def bse.use_of(u: B.Use, +n: Nat, s: String) -> {FBs.get_req.base(n, u, FBg.get_ask(s)) == FBs.get_req.use(Budget.sp_use_tag(u), n, s) : Wr.Dec<FBs.Req>}:
  match u:
    case B.Work{}:
      {==}
    case B.Final{}:
      {==}
    case B.Side{}:
      {==}

# a spelled request that fits reads back, the rest untouched
def bse.reads(q: FBs.Req, +rest: String, h: {BudgetShare.sh_fit_req(q) == True{} : Bool}) -> {FBs.get_req(BudgetShare.sh_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FBs.Req>}:
  match q:
    case FBs.Req{+n, +u, +base, +keep, +want, +less, +free, +now, +until}:
      +h0 = h
      +b8 = Bool.and(LawsBase.wire_fits(now), LawsBase.wire_fits(until))
      +b7 = Bool.and(Budget.sp_fit_amt(free), b8)
      +b6 = Bool.and(Budget.sp_fit_asks(less), b7)
      +b5 = Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), b6)
      +b4 = Bool.and(Budget.sp_fit_ask(want), b5)
      +b3 = Bool.and(Budget.sp_fit_ask(keep), b4)
      +b2 = Bool.and(Budget.sp_fit_ask(base), b3)
      +fn = BE.be.and_l(LawsBase.wire_fits(n), b2, h0)
      +h1 = BE.be.and_r(LawsBase.wire_fits(n), b2, h0)
      +fb = BE.be.and_l(Budget.sp_fit_ask(base), b3, h1)
      +h2 = BE.be.and_r(Budget.sp_fit_ask(base), b3, h1)
      +fk = BE.be.and_l(Budget.sp_fit_ask(keep), b4, h2)
      +h3 = BE.be.and_r(Budget.sp_fit_ask(keep), b4, h2)
      +fw = BE.be.and_l(Budget.sp_fit_ask(want), b5, h3)
      +h4 = BE.be.and_r(Budget.sp_fit_ask(want), b5, h3)
      +fc = BE.be.and_l(LawsBase.wire_fits(List.length(&2, B.Ask, less)), b6, h4)
      +h5 = BE.be.and_r(LawsBase.wire_fits(List.length(&2, B.Ask, less)), b6, h4)
      +fl = BE.be.and_l(Budget.sp_fit_asks(less), b7, h5)
      +h6 = BE.be.and_r(Budget.sp_fit_asks(less), b7, h5)
      +ff = BE.be.and_l(Budget.sp_fit_amt(free), b8, h6)
      +h7 = BE.be.and_r(Budget.sp_fit_amt(free), b8, h6)
      +fnow = BE.be.and_l(LawsBase.wire_fits(now), LawsBase.wire_fits(until), h7)
      +fu = BE.be.and_r(LawsBase.wire_fits(now), LawsBase.wire_fits(until), h7)
      +s9 = Wr.put_nat(until, rest)
      +s8 = Wr.put_nat(now, s9)
      +s7 = Budget.sp_w_amt(free, s8)
      +s6 = Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, s7)
      +s5 = Budget.sp_w_ask(want, s6)
      +s4 = Budget.sp_w_ask(keep, s5)
      +s3 = Budget.sp_w_ask(base, s4)
      +s2 = Wr.put_nat(Budget.sp_use_tag(u), s3)
      +v = {Wr.Got{FBs.Req{n, u, base, keep, want, less, free, now, until}, rest} : Wr.Dec<FBs.Req>}
      %BE.be.nat(n, s2, fn) : {FBs.get_req.n(_) == v : Wr.Dec<FBs.Req>}
      %BE.be.use_nat(u, s3) : {FBs.get_req.tag(n, _) == v : Wr.Dec<FBs.Req>}
      %bse.use_of(u, n, s3) : {_ == v : Wr.Dec<FBs.Req>}
      %BE.be.ask(base, s4, fb) : {FBs.get_req.base(n, u, _) == v : Wr.Dec<FBs.Req>}
      %BE.be.ask(keep, s5, fk) : {FBs.get_req.keep(n, u, base, _) == v : Wr.Dec<FBs.Req>}
      %BE.be.ask(want, s6, fw) : {FBs.get_req.want(n, u, base, keep, _) == v : Wr.Dec<FBs.Req>}
      %BE.be.asks(less, s7, fc, fl) : {FBs.get_req.less(n, u, base, keep, want, _) == v : Wr.Dec<FBs.Req>}
      %BE.be.amt(free, s8, ff) : {FBs.get_req.free(n, u, base, keep, want, less, _) == v : Wr.Dec<FBs.Req>}
      %BE.be.nat(now, s9, fnow) : {FBs.get_req.now(n, u, base, keep, want, less, free, _) == v : Wr.Dec<FBs.Req>}
      %BE.be.nat(until, rest, fu) : {FBs.get_req.until(n, u, base, keep, want, less, free, now, _) == v : Wr.Dec<FBs.Req>}
      {==}

# the entry answers a request read whole with the model's start spelled
def bse.reply(q: FBs.Req) -> {FBs.ffi.got(Wr.Got{q, ""}) == BudgetShare.sh_reply(q) : String}:
  match q:
    case FBs.Req{n, u, base, keep, want, less, free, now, until}:
      {==}

# Exactness: Nats
# ---------------

# what a Nat reader's answer says about its input s
def bsx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def bsx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> bsx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def bsx.nat(+s: String) -> bsx.NP(s, Wr.get_nat(s)):
  bsx.nat.at(s, Wr.get_nat(s), {==})

# Exactness: amounts and asks
# ---------------------------

# what an amount reader's answer says about its input s
def bsx.AP(s: String, d: Wr.Dec<B.Amt>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Budget.sp_w_amt(x, r) : String} & {Budget.sp_fit_amt(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def bsx.amt_r(-s: String, +c: Nat, +k: Nat, +n: Nat, +s3: String, pre: {s == Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, s3))) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, np: bsx.NP(s3, d)) -> bsx.AP(s, FBg.get_amt.r(c, k, n, d)):
  match d:
    case Wr.Got{+r, +s4}:
      (e, f) = np
      (Equal.trans(String, s, Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, s3))), Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, Wr.put_nat(r, s4)))), pre, Equal.cong(String, String, z => Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, z))), s3, Wr.put_nat(r, s4), e)), LBool.cb_and_intro(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(r))), fc, LBool.cb_and_intro(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(r)), fk, LBool.cb_and_intro(LawsBase.wire_fits(n), LawsBase.wire_fits(r), fn, f))))
    case Wr.Bad{}:
      Unit{}

def bsx.amt_n(-s: String, +c: Nat, +k: Nat, +s2: String, pre: {s == Wr.put_nat(c, Wr.put_nat(k, s2)) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, np: bsx.NP(s2, d)) -> bsx.AP(s, FBg.get_amt.n(c, k, d)):
  match d:
    case Wr.Got{+n, +s3}:
      (e, f) = np
      bsx.amt_r(s, c, k, n, s3, Equal.trans(String, s, Wr.put_nat(c, Wr.put_nat(k, s2)), Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(c, Wr.put_nat(k, z)), s2, Wr.put_nat(n, s3), e)), fc, fk, f, Wr.get_nat(s3), bsx.nat(s3))
    case Wr.Bad{}:
      Unit{}

def bsx.amt_k(-s: String, +c: Nat, +s1: String, pre: {s == Wr.put_nat(c, s1) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, np: bsx.NP(s1, d)) -> bsx.AP(s, FBg.get_amt.k(c, d)):
  match d:
    case Wr.Got{+k, +s2}:
      (e, f) = np
      bsx.amt_n(s, c, k, s2, Equal.trans(String, s, Wr.put_nat(c, s1), Wr.put_nat(c, Wr.put_nat(k, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(c, z), s1, Wr.put_nat(k, s2), e)), fc, f, Wr.get_nat(s2), bsx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def bsx.amt_c(-s: String, d: Wr.Dec<Nat>, np: bsx.NP(s, d)) -> bsx.AP(s, FBg.get_amt.c(d)):
  match d:
    case Wr.Got{+c, +s1}:
      (e, f) = np
      bsx.amt_k(s, c, s1, e, f, Wr.get_nat(s1), bsx.nat(s1))
    case Wr.Bad{}:
      Unit{}

# the amount reader accepts only spelled amounts that fit
def bsx.amt(+s: String) -> bsx.AP(s, FBg.get_amt(s)):
  bsx.amt_c(s, Wr.get_nat(s), bsx.nat(s))

# what an ask reader's answer says about its input s
def bsx.KP(s: String, d: Wr.Dec<B.Ask>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Budget.sp_w_ask(x, r) : String} & {Budget.sp_fit_ask(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def bsx.ask_ms(-s: String, +x: B.Amt, +s1: String, pre: {s == Budget.sp_w_amt(x, s1) : String}, fx: {Budget.sp_fit_amt(x) == True{} : Bool}, d: Wr.Dec<Nat>, np: bsx.NP(s1, d)) -> bsx.KP(s, FBg.get_ask.ms(x, d)):
  match d:
    case Wr.Got{+m, +s2}:
      (e, f) = np
      (Equal.trans(String, s, Budget.sp_w_amt(x, s1), Budget.sp_w_amt(x, Wr.put_nat(m, s2)), pre, Equal.cong(String, String, z => Budget.sp_w_amt(x, z), s1, Wr.put_nat(m, s2), e)), LBool.cb_and_intro(Budget.sp_fit_amt(x), LawsBase.wire_fits(m), fx, f))
    case Wr.Bad{}:
      Unit{}

def bsx.ask_amt(-s: String, d: Wr.Dec<B.Amt>, ap: bsx.AP(s, d)) -> bsx.KP(s, FBg.get_ask.amt(d)):
  match d:
    case Wr.Got{+x, +s1}:
      (e, f) = ap
      bsx.ask_ms(s, x, s1, e, f, Wr.get_nat(s1), bsx.nat(s1))
    case Wr.Bad{}:
      Unit{}

# the ask reader accepts only spelled asks that fit
def bsx.ask(+s: String) -> bsx.KP(s, FBg.get_ask(s)):
  bsx.ask_amt(s, FBg.get_amt(s), bsx.amt(s))

def bsx.ask_at(+s: String, -d: Wr.Dec<B.Ask>, ed: {FBg.get_ask(s) == d : Wr.Dec<B.Ask>}) -> bsx.KP(s, d):
  %ed : bsx.KP(s, _)
  bsx.ask(s)

# Exactness: the offers
# ---------------------

# what the item reader's answer says about its input s (k asks)
def bsx.IP(s: String, k: Nat, d: Wr.Dec<List<&2, B.Ask>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, r) : String} & ({List.length(&2, B.Ask, xs) == k : Nat} & {Budget.sp_fit_asks(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# an ask before asks read
def bsx.cons(-s: String, +c: B.Ask, +r1: String, -k: Nat, d: Wr.Dec<List<&2, B.Ask>>, ih: bsx.IP(r1, k, d), cp: {s == Budget.sp_w_ask(c, r1) : String} & {Budget.sp_fit_ask(c) == True{} : Bool}) -> bsx.IP(s, 1n+k, LawsBase.wire_items.cons(B.Ask, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (Equal.trans(String, s, Budget.sp_w_ask(c, r1), Budget.sp_w_ask(c, LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, r)), ec, Equal.cong(String, String, z => Budget.sp_w_ask(c, z), r1, LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, r), e1)), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, B.Ask, xs), k, e2), LBool.cb_and_intro(Budget.sp_fit_ask(c), Budget.sp_fit_asks(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

# mm + 1 asks, the first read from s as cur
def bsx.items(mm: Nat, cur: Wr.Dec<B.Ask>, +s: String, er: {FBg.get_ask(s) == cur : Wr.Dec<B.Ask>}) -> bsx.IP(s, 1n+mm, LawsBase.wire_items.then(B.Ask, cur, r => LawsBase.wire_items(~B.Ask, ~FBg.get_ask, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      bsx.cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), bsx.ask_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      bsx.cons(s, c, r1, 1n+k, LawsBase.wire_items.then(B.Ask, FBg.get_ask(r1), r => LawsBase.wire_items(~B.Ask, ~FBg.get_ask, k, r)), bsx.items(k, FBg.get_ask(r1), r1, {==}), bsx.ask_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def bsx.items_of(k: Nat, +s: String) -> bsx.IP(s, k, LawsBase.wire_items(~B.Ask, ~FBg.get_ask, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      bsx.items(mm, FBg.get_ask(s), s, {==})

# what the offer list reader's answer says about its input s
def bsx.LP(s: String, d: Wr.Dec<List<&2, B.Ask>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~B.Ask, ~Budget.sp_w_ask, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, B.Ask, xs)) == True{} : Bool} & {Budget.sp_fit_asks(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def bsx.list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, B.Ask>>, ip: bsx.IP(s1, k, d)) -> bsx.LP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, B.Ask, xs)
      +w = LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, r)
      +es = Equal.trans(String, s, Wr.put_nat(k, s1), Wr.put_nat(k, w), en, Equal.cong(String, String, z => Wr.put_nat(k, z), s1, w, e1))
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ep = Equal.trans(String, Wr.put_nat(n, w), LawsBase.wire_dec(n, w), Wr.put_list(~B.Ask, ~Budget.sp_w_ask, xs, r), LAWireDec.wdec.nat(n, w), Equal.sym(String, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, xs, r), LawsBase.wire_dec(n, w), Wire.wire_list_spells_items(~B.Ask, ~Budget.sp_w_ask, xs, r)))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), Wr.put_list(~B.Ask, ~Budget.sp_w_ask, xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ep), (fl, e3))
    case Wr.Bad{}:
      Unit{}

def bsx.count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> bsx.LP(s, LawsBase.wire_read_list.count(~B.Ask, ~FBg.get_ask, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      bsx.list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~B.Ask, ~FBg.get_ask, k, s1), bsx.items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the offer list reader accepts only spelled lists that fit
def bsx.asks(+s: String) -> bsx.LP(s, Wr.get_list(~B.Ask, ~FBg.get_ask, s)):
  %Equal.sym(Wr.Dec<List<&2, B.Ask>>, Wr.get_list(~B.Ask, ~FBg.get_ask, s), LawsBase.wire_read_list(~B.Ask, ~FBg.get_ask, s), Wire.wire_list_reads_items(~B.Ask, ~FBg.get_ask, s)) : bsx.LP(s, _)
  bsx.count(s, Wr.get_nat(s), {==})

# Exactness: the request
# ----------------------

# the spelling of a request up to the field after each one, then rest
def bsx.p_base(+n: Nat, u: B.Use, rest: String) -> String:
  Wr.put_nat(n, Wr.put_nat(Budget.sp_use_tag(u), rest))

def bsx.p_keep(+n: Nat, u: B.Use, base: B.Ask, rest: String) -> String:
  bsx.p_base(n, u, Budget.sp_w_ask(base, rest))

def bsx.p_want(+n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, rest: String) -> String:
  bsx.p_keep(n, u, base, Budget.sp_w_ask(keep, rest))

def bsx.p_less(+n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, rest: String) -> String:
  bsx.p_want(n, u, base, keep, Budget.sp_w_ask(want, rest))

def bsx.p_free(+n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, rest: String) -> String:
  bsx.p_less(n, u, base, keep, want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, rest))

def bsx.p_now(+n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, free: B.Amt, rest: String) -> String:
  bsx.p_free(n, u, base, keep, want, less, Budget.sp_w_amt(free, rest))

def bsx.p_until(+n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, free: B.Amt, now: Nat, rest: String) -> String:
  bsx.p_now(n, u, base, keep, want, less, free, Wr.put_nat(now, rest))

# what the request reader's answer says about its input s
def bsx.RP(s: String, d: Wr.Dec<FBs.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == BudgetShare.sh_w_req(q, r) : String} & {BudgetShare.sh_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# nine that hold: all hold
def bsx.fit9(-a1: Bool, -a2: Bool, -a3: Bool, -a4: Bool, -a5: Bool, -a6: Bool, -a7: Bool, -a8: Bool, -a9: Bool, e1: {a1 == True{} : Bool}, e2: {a2 == True{} : Bool}, e3: {a3 == True{} : Bool}, e4: {a4 == True{} : Bool}, e5: {a5 == True{} : Bool}, e6: {a6 == True{} : Bool}, e7: {a7 == True{} : Bool}, e8: {a8 == True{} : Bool}, e9: {a9 == True{} : Bool}) -> {Bool.and(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(a8, a9)))))))) == True{} : Bool}:
  LBool.cb_and_intro(a1, Bool.and(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(a8, a9))))))), e1, LBool.cb_and_intro(a2, Bool.and(a3, Bool.and(a4, Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(a8, a9)))))), e2, LBool.cb_and_intro(a3, Bool.and(a4, Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(a8, a9))))), e3, LBool.cb_and_intro(a4, Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(a8, a9)))), e4, LBool.cb_and_intro(a5, Bool.and(a6, Bool.and(a7, Bool.and(a8, a9))), e5, LBool.cb_and_intro(a6, Bool.and(a7, Bool.and(a8, a9)), e6, LBool.cb_and_intro(a7, Bool.and(a8, a9), e7, LBool.cb_and_intro(a8, a9, e8, e9))))))))

def bsx.until(-s: String, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +free: B.Amt, +now: Nat, +s9: String, pre: {s == bsx.p_until(n, u, base, keep, want, less, free, now, s9) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fb: {Budget.sp_fit_ask(base) == True{} : Bool}, fk: {Budget.sp_fit_ask(keep) == True{} : Bool}, fw: {Budget.sp_fit_ask(want) == True{} : Bool}, fc: {LawsBase.wire_fits(List.length(&2, B.Ask, less)) == True{} : Bool}, fl: {Budget.sp_fit_asks(less) == True{} : Bool}, ff: {Budget.sp_fit_amt(free) == True{} : Bool}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<Nat>, np: bsx.NP(s9, d)) -> bsx.RP(s, FBs.get_req.until(n, u, base, keep, want, less, free, now, d)):
  match d:
    case Wr.Got{+until, +r}:
      (e, f) = np
      (Equal.trans(String, s, bsx.p_until(n, u, base, keep, want, less, free, now, s9), bsx.p_until(n, u, base, keep, want, less, free, now, Wr.put_nat(until, r)), pre, Equal.cong(String, String, z => bsx.p_until(n, u, base, keep, want, less, free, now, z), s9, Wr.put_nat(until, r), e)), bsx.fit9(LawsBase.wire_fits(n), Budget.sp_fit_ask(base), Budget.sp_fit_ask(keep), Budget.sp_fit_ask(want), LawsBase.wire_fits(List.length(&2, B.Ask, less)), Budget.sp_fit_asks(less), Budget.sp_fit_amt(free), LawsBase.wire_fits(now), LawsBase.wire_fits(until), fn, fb, fk, fw, fc, fl, ff, fnow, f))
    case Wr.Bad{}:
      Unit{}

def bsx.now(-s: String, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +free: B.Amt, +s8: String, pre: {s == bsx.p_now(n, u, base, keep, want, less, free, s8) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fb: {Budget.sp_fit_ask(base) == True{} : Bool}, fk: {Budget.sp_fit_ask(keep) == True{} : Bool}, fw: {Budget.sp_fit_ask(want) == True{} : Bool}, fc: {LawsBase.wire_fits(List.length(&2, B.Ask, less)) == True{} : Bool}, fl: {Budget.sp_fit_asks(less) == True{} : Bool}, ff: {Budget.sp_fit_amt(free) == True{} : Bool}, d: Wr.Dec<Nat>, np: bsx.NP(s8, d)) -> bsx.RP(s, FBs.get_req.now(n, u, base, keep, want, less, free, d)):
  match d:
    case Wr.Got{+now, +s9}:
      (e, f) = np
      bsx.until(s, n, u, base, keep, want, less, free, now, s9, Equal.trans(String, s, bsx.p_now(n, u, base, keep, want, less, free, s8), bsx.p_now(n, u, base, keep, want, less, free, Wr.put_nat(now, s9)), pre, Equal.cong(String, String, z => bsx.p_now(n, u, base, keep, want, less, free, z), s8, Wr.put_nat(now, s9), e)), fn, fb, fk, fw, fc, fl, ff, f, Wr.get_nat(s9), bsx.nat(s9))
    case Wr.Bad{}:
      Unit{}

def bsx.free(-s: String, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +s7: String, pre: {s == bsx.p_free(n, u, base, keep, want, less, s7) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fb: {Budget.sp_fit_ask(base) == True{} : Bool}, fk: {Budget.sp_fit_ask(keep) == True{} : Bool}, fw: {Budget.sp_fit_ask(want) == True{} : Bool}, fc: {LawsBase.wire_fits(List.length(&2, B.Ask, less)) == True{} : Bool}, fl: {Budget.sp_fit_asks(less) == True{} : Bool}, d: Wr.Dec<B.Amt>, ap: bsx.AP(s7, d)) -> bsx.RP(s, FBs.get_req.free(n, u, base, keep, want, less, d)):
  match d:
    case Wr.Got{+free, +s8}:
      (e, f) = ap
      bsx.now(s, n, u, base, keep, want, less, free, s8, Equal.trans(String, s, bsx.p_free(n, u, base, keep, want, less, s7), bsx.p_free(n, u, base, keep, want, less, Budget.sp_w_amt(free, s8)), pre, Equal.cong(String, String, z => bsx.p_free(n, u, base, keep, want, less, z), s7, Budget.sp_w_amt(free, s8), e)), fn, fb, fk, fw, fc, fl, f, Wr.get_nat(s8), bsx.nat(s8))
    case Wr.Bad{}:
      Unit{}

def bsx.less(-s: String, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +want: B.Ask, +s6: String, pre: {s == bsx.p_less(n, u, base, keep, want, s6) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fb: {Budget.sp_fit_ask(base) == True{} : Bool}, fk: {Budget.sp_fit_ask(keep) == True{} : Bool}, fw: {Budget.sp_fit_ask(want) == True{} : Bool}, d: Wr.Dec<List<&2, B.Ask>>, lp: bsx.LP(s6, d)) -> bsx.RP(s, FBs.get_req.less(n, u, base, keep, want, d)):
  match d:
    case Wr.Got{+less, +s7}:
      (e, (fc, fl)) = lp
      bsx.free(s, n, u, base, keep, want, less, s7, Equal.trans(String, s, bsx.p_less(n, u, base, keep, want, s6), bsx.p_less(n, u, base, keep, want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, s7)), pre, Equal.cong(String, String, z => bsx.p_less(n, u, base, keep, want, z), s6, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, s7), e)), fn, fb, fk, fw, fc, fl, FBg.get_amt(s7), bsx.amt(s7))
    case Wr.Bad{}:
      Unit{}

def bsx.want(-s: String, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +s5: String, pre: {s == bsx.p_want(n, u, base, keep, s5) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fb: {Budget.sp_fit_ask(base) == True{} : Bool}, fk: {Budget.sp_fit_ask(keep) == True{} : Bool}, d: Wr.Dec<B.Ask>, kp: bsx.KP(s5, d)) -> bsx.RP(s, FBs.get_req.want(n, u, base, keep, d)):
  match d:
    case Wr.Got{+want, +s6}:
      (e, f) = kp
      bsx.less(s, n, u, base, keep, want, s6, Equal.trans(String, s, bsx.p_want(n, u, base, keep, s5), bsx.p_want(n, u, base, keep, Budget.sp_w_ask(want, s6)), pre, Equal.cong(String, String, z => bsx.p_want(n, u, base, keep, z), s5, Budget.sp_w_ask(want, s6), e)), fn, fb, fk, f, Wr.get_list(~B.Ask, ~FBg.get_ask, s6), bsx.asks(s6))
    case Wr.Bad{}:
      Unit{}

def bsx.keep(-s: String, +n: Nat, +u: B.Use, +base: B.Ask, +s4: String, pre: {s == bsx.p_keep(n, u, base, s4) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fb: {Budget.sp_fit_ask(base) == True{} : Bool}, d: Wr.Dec<B.Ask>, kp: bsx.KP(s4, d)) -> bsx.RP(s, FBs.get_req.keep(n, u, base, d)):
  match d:
    case Wr.Got{+keep, +s5}:
      (e, f) = kp
      bsx.want(s, n, u, base, keep, s5, Equal.trans(String, s, bsx.p_keep(n, u, base, s4), bsx.p_keep(n, u, base, Budget.sp_w_ask(keep, s5)), pre, Equal.cong(String, String, z => bsx.p_keep(n, u, base, z), s4, Budget.sp_w_ask(keep, s5), e)), fn, fb, f, FBg.get_ask(s5), bsx.ask(s5))
    case Wr.Bad{}:
      Unit{}

def bsx.base(-s: String, +n: Nat, +u: B.Use, +s3: String, pre: {s == bsx.p_base(n, u, s3) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<B.Ask>, kp: bsx.KP(s3, d)) -> bsx.RP(s, FBs.get_req.base(n, u, d)):
  match d:
    case Wr.Got{+base, +s4}:
      (e, f) = kp
      bsx.keep(s, n, u, base, s4, Equal.trans(String, s, bsx.p_base(n, u, s3), bsx.p_base(n, u, Budget.sp_w_ask(base, s4)), pre, Equal.cong(String, String, z => bsx.p_base(n, u, z), s3, Budget.sp_w_ask(base, s4), e)), fn, f, FBg.get_ask(s4), bsx.ask(s4))
    case Wr.Bad{}:
      Unit{}

# the use of tag t
def bsx.use(t: Nat, -s: String, +n: Nat, +s2: String, pre: {s == Wr.put_nat(n, Wr.put_nat(t, s2)) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> bsx.RP(s, FBs.get_req.use(t, n, s2)):
  match t:
    case 0n:
      bsx.base(s, n, B.Work{}, s2, pre, fn, FBg.get_ask(s2), bsx.ask(s2))
    case 1n+a:
      match a:
        case 0n:
          bsx.base(s, n, B.Final{}, s2, pre, fn, FBg.get_ask(s2), bsx.ask(s2))
        case 1n+b:
          match b:
            case 0n:
              bsx.base(s, n, B.Side{}, s2, pre, fn, FBg.get_ask(s2), bsx.ask(s2))
            case 1n+c:
              Unit{}

def bsx.tag(-s: String, +n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, np: bsx.NP(s1, d)) -> bsx.RP(s, FBs.get_req.tag(n, d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e, f) = np
      bsx.use(t, s, n, s2, Equal.trans(String, s, Wr.put_nat(n, s1), Wr.put_nat(n, Wr.put_nat(t, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(n, z), s1, Wr.put_nat(t, s2), e)), fn)
    case Wr.Bad{}:
      Unit{}

def bsx.n(-s: String, d: Wr.Dec<Nat>, np: bsx.NP(s, d)) -> bsx.RP(s, FBs.get_req.n(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = np
      bsx.tag(s, n, s1, e, f, Wr.get_nat(s1), bsx.nat(s1))
    case Wr.Bad{}:
      Unit{}

# the request reader accepts only spelled requests that fit
def bsx.req(+s: String) -> bsx.RP(s, FBs.get_req(s)):
  bsx.n(s, Wr.get_nat(s), bsx.nat(s))
