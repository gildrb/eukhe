# eukhe: the proof of LAW limits_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only for an input that is the
# spelling of q before rest, every number, count and length within the
# wire (lxe.req, stage by stage: a Nat by wire_nat_exact and
# wire_nat_decoded_fits, a T|F by wire_bool_exact, a string by
# wire_str_exact and wire_str_decoded_fits, a list of strings by
# wire_strs_exact, a list of other items by wire_list_reads_items, item by
# item, and wire_list_spells_items, the budget's asks, amounts and accounts
# by budget's lemmas); the entry answers the model's answer only for a
# request read whole with nothing left (lxe.top).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../bend/ffi_limits.bend as FL
import ../../bend/ffi_budget.bend as FB
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/budget.bend as Budget
import ../../laws/limits.bend as Limits
import ../budget/base/exact.bend as BX
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../wire/base/dec.bend as LAWireDec
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_strs_exact.bend as PWireStrsExact
import ../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../wire/wire_strs_spells.bend as PWireStrsSpells
import ../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../wire/wire_list_spells_items.bend as PWireListSpellsItems

# an equation on the input carried into a context F
def lxe.tr(-s: String, -a: String, -b: String, -F: String -> String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Tags
# ----

# what the toggle reader's answer says about its input s
def lxe.TP(s: String, d: Wr.Dec<L.Toggle>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Wr.put_bool(Limits.sp_on(t), r) : String}
    case Wr.Bad{}:
      Unit

def lxe.tog_of(b: Bool, -s: String, -r: String, e: {s == Wr.put_bool(b, r) : String}) -> lxe.TP(s, FL.get_toggle.of(b, r)):
  match b:
    case True{}:
      e
    case False{}:
      e

def lxe.tog_b(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> lxe.TP(s, FL.get_toggle.b(d)):
  match d:
    case Wr.Got{+b, +r}:
      lxe.tog_of(b, s, r, Wire.wire_bool_exact(s, b, r, ed))
    case Wr.Bad{}:
      Unit{}

# the toggle reader accepts only T and F
def lxe.tog(+s: String) -> lxe.TP(s, FL.get_toggle(s)):
  lxe.tog_b(s, Wr.get_bool(s), {==})

# what the kind reader's answer says about its input s
def lxe.KP(s: String, d: Wr.Dec<L.Run>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == Wr.put_nat(Limits.sp_kind_tag(k), r) : String}
    case Wr.Bad{}:
      Unit

def lxe.kind_of(n: Nat, -s: String, -r: String, e: {s == Wr.put_nat(n, r) : String}) -> lxe.KP(s, FL.get_kind.of(n, r)):
  match n:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
    case 4n:
      e
    case 5n:
      e
    case 6n+p:
      Unit{}

def lxe.kind_n(-s: String, d: Wr.Dec<Nat>, np: BX.bx.NP(s, d)) -> lxe.KP(s, FL.get_kind.n(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      lxe.kind_of(n, s, r, e)
    case Wr.Bad{}:
      Unit{}

# the kind reader accepts only spelled kinds
def lxe.kind(+s: String) -> lxe.KP(s, FL.get_kind(s)):
  lxe.kind_n(s, Wr.get_nat(s), BX.bx.nat(s))

# what the auth reader's answer says about its input s
def lxe.AP(s: String, d: Wr.Dec<L.Auth>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_nat(Limits.sp_auth_tag(a), r) : String}
    case Wr.Bad{}:
      Unit

def lxe.auth_of(n: Nat, -s: String, -r: String, e: {s == Wr.put_nat(n, r) : String}) -> lxe.AP(s, FL.get_auth.of(n, r)):
  match n:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n+p:
      Unit{}

def lxe.auth_n(-s: String, d: Wr.Dec<Nat>, np: BX.bx.NP(s, d)) -> lxe.AP(s, FL.get_auth.n(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      lxe.auth_of(n, s, r, e)
    case Wr.Bad{}:
      Unit{}

# the auth reader accepts only spelled auths
def lxe.auth(+s: String) -> lxe.AP(s, FL.get_auth(s)):
  lxe.auth_n(s, Wr.get_nat(s), BX.bx.nat(s))

# what the scale reader's answer says about its input s
def lxe.SP(s: String, d: Wr.Dec<L.Scale>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == Wr.put_nat(Limits.sp_scale_tag(c), r) : String}
    case Wr.Bad{}:
      Unit

def lxe.scale_of(n: Nat, -s: String, -r: String, e: {s == Wr.put_nat(n, r) : String}) -> lxe.SP(s, FL.get_scale.of(n, r)):
  match n:
    case 0n:
      e
    case 1n:
      e
    case 2n+p:
      Unit{}

def lxe.scale_n(-s: String, d: Wr.Dec<Nat>, np: BX.bx.NP(s, d)) -> lxe.SP(s, FL.get_scale.n(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      lxe.scale_of(n, s, r, e)
    case Wr.Bad{}:
      Unit{}

# the scale reader accepts only spelled scales
def lxe.scale(+s: String) -> lxe.SP(s, FL.get_scale(s)):
  lxe.scale_n(s, Wr.get_nat(s), BX.bx.nat(s))

# Limits
# ------

# what the limit reader's answer says about its input s
def lxe.VP(s: String, d: Wr.Dec<L.Val>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == Limits.sp_w_val(v, r) : String} & {Limits.sp_fit_val(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def lxe.val_at(-s: String, -r: String, pre: {s == Wr.put_nat(1n, r) : String}, d: Wr.Dec<Nat>, np: BX.bx.NP(r, d)) -> lxe.VP(s, FL.get_val.at(d)):
  match d:
    case Wr.Got{+v, +r2}:
      (e, f) = np
      (lxe.tr(s, r, Wr.put_nat(v, r2), z => Wr.put_nat(1n, z), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def lxe.val_of(n: Nat, -s: String, +r: String, e: {s == Wr.put_nat(n, r) : String}) -> lxe.VP(s, FL.get_val.of(n, r)):
  match n:
    case 0n:
      (e, {==})
    case 1n:
      lxe.val_at(s, r, e, Wr.get_nat(r), BX.bx.nat(r))
    case 2n:
      (e, {==})
    case 3n+p:
      Unit{}

def lxe.val_n(-s: String, d: Wr.Dec<Nat>, np: BX.bx.NP(s, d)) -> lxe.VP(s, FL.get_val.n(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      lxe.val_of(n, s, r, e)
    case Wr.Bad{}:
      Unit{}

# the limit reader accepts only spelled limits that fit
def lxe.val(+s: String) -> lxe.VP(s, FL.get_val(s)):
  lxe.val_n(s, Wr.get_nat(s), BX.bx.nat(s))

# what the limits reader's answer says about its input s
def lxe.LP(s: String, d: Wr.Dec<L.Lims>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Limits.sp_w_lims(l, r) : String} & {Limits.sp_fit_lims(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# limits, field by field (the last field first: a stage calls the next)
def lxe.lims_r(-s: String, +c: L.Val, +k: L.Val, +m: L.Val, +n: L.Val, -sk: String, pre: {s == Limits.sp_w_val(c, Limits.sp_w_val(k, Limits.sp_w_val(m, Limits.sp_w_val(n, sk)))) : String}, fc: {Limits.sp_fit_val(c) == True{} : Bool}, fk: {Limits.sp_fit_val(k) == True{} : Bool}, fm: {Limits.sp_fit_val(m) == True{} : Bool}, fn: {Limits.sp_fit_val(n) == True{} : Bool}, d: Wr.Dec<L.Val>, np: lxe.VP(sk, d)) -> lxe.LP(s, FL.get_lims.r(c, k, m, n, d)):
  match d:
    case Wr.Got{+r, +sn}:
      (e, fr) = np
      (lxe.tr(s, sk, Limits.sp_w_val(r, sn), z => Limits.sp_w_val(c, Limits.sp_w_val(k, Limits.sp_w_val(m, Limits.sp_w_val(n, z)))), pre, e), LBool.cb_and_intro(Limits.sp_fit_val(c), Bool.and(Limits.sp_fit_val(k), Bool.and(Limits.sp_fit_val(m), Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r)))), fc, LBool.cb_and_intro(Limits.sp_fit_val(k), Bool.and(Limits.sp_fit_val(m), Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r))), fk, LBool.cb_and_intro(Limits.sp_fit_val(m), Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r)), fm, LBool.cb_and_intro(Limits.sp_fit_val(n), Limits.sp_fit_val(r), fn, fr)))))
    case Wr.Bad{}:
      Unit{}

def lxe.lims_n(-s: String, +c: L.Val, +k: L.Val, +m: L.Val, -sk: String, pre: {s == Limits.sp_w_val(c, Limits.sp_w_val(k, Limits.sp_w_val(m, sk))) : String}, fc: {Limits.sp_fit_val(c) == True{} : Bool}, fk: {Limits.sp_fit_val(k) == True{} : Bool}, fm: {Limits.sp_fit_val(m) == True{} : Bool}, d: Wr.Dec<L.Val>, np: lxe.VP(sk, d)) -> lxe.LP(s, FL.get_lims.n(c, k, m, d)):
  match d:
    case Wr.Got{+n, +sn}:
      (e, fn) = np
      lxe.lims_r(s, c, k, m, n, sn, lxe.tr(s, sk, Limits.sp_w_val(n, sn), z => Limits.sp_w_val(c, Limits.sp_w_val(k, Limits.sp_w_val(m, z))), pre, e), fc, fk, fm, fn, FL.get_val(sn), lxe.val(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.lims_m(-s: String, +c: L.Val, +k: L.Val, -sk: String, pre: {s == Limits.sp_w_val(c, Limits.sp_w_val(k, sk)) : String}, fc: {Limits.sp_fit_val(c) == True{} : Bool}, fk: {Limits.sp_fit_val(k) == True{} : Bool}, d: Wr.Dec<L.Val>, np: lxe.VP(sk, d)) -> lxe.LP(s, FL.get_lims.m(c, k, d)):
  match d:
    case Wr.Got{+m, +sn}:
      (e, fm) = np
      lxe.lims_n(s, c, k, m, sn, lxe.tr(s, sk, Limits.sp_w_val(m, sn), z => Limits.sp_w_val(c, Limits.sp_w_val(k, z)), pre, e), fc, fk, fm, FL.get_val(sn), lxe.val(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.lims_k(-s: String, +c: L.Val, -sk: String, pre: {s == Limits.sp_w_val(c, sk) : String}, fc: {Limits.sp_fit_val(c) == True{} : Bool}, d: Wr.Dec<L.Val>, np: lxe.VP(sk, d)) -> lxe.LP(s, FL.get_lims.k(c, d)):
  match d:
    case Wr.Got{+k, +sn}:
      (e, fk) = np
      lxe.lims_m(s, c, k, sn, lxe.tr(s, sk, Limits.sp_w_val(k, sn), z => Limits.sp_w_val(c, z), pre, e), fc, fk, FL.get_val(sn), lxe.val(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.lims_c(-s: String, d: Wr.Dec<L.Val>, np: lxe.VP(s, d)) -> lxe.LP(s, FL.get_lims.c(d)):
  match d:
    case Wr.Got{+c, +sn}:
      (e, fc) = np
      lxe.lims_k(s, c, sn, e, fc, FL.get_val(sn), lxe.val(sn))
    case Wr.Bad{}:
      Unit{}

# the limits reader accepts only spelled limits that fit
def lxe.lims(+s: String) -> lxe.LP(s, FL.get_lims(s)):
  lxe.lims_c(s, FL.get_val(s), lxe.val(s))

# Lists
# -----

# what the item reader's answer says about its input s (k limits)
def lxe.LIP(s: String, k: Nat, d: Wr.Dec<List<&2, L.Lims>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_put_items(~L.Lims, ~Limits.sp_w_lims, xs, r) : String} & ({List.length(&2, L.Lims, xs) == k : Nat} & {Limits.sp_fit_limss(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def lxe.lims_at(+s: String, -d: Wr.Dec<L.Lims>, ed: {FL.get_lims(s) == d : Wr.Dec<L.Lims>}) -> lxe.LP(s, d):
  %ed : lxe.LP(s, _)
  lxe.lims(s)

# an item before items read
def lxe.lims_cons(-s: String, +c: L.Lims, +r1: String, -k: Nat, d: Wr.Dec<List<&2, L.Lims>>, ih: lxe.LIP(r1, k, d), cp: lxe.LP(s, Wr.Got{c, r1})) -> lxe.LIP(s, 1n+k, LawsBase.wire_items.cons(L.Lims, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (lxe.tr(s, r1, LawsBase.wire_put_items(~L.Lims, ~Limits.sp_w_lims, xs, r), z => Limits.sp_w_lims(c, z), ec, e1), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, L.Lims, xs), k, e2), LBool.cb_and_intro(Limits.sp_fit_lims(c), Limits.sp_fit_limss(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

# mm + 1 items, the first read from s as cur
def lxe.lims_items(mm: Nat, cur: Wr.Dec<L.Lims>, +s: String, er: {FL.get_lims(s) == cur : Wr.Dec<L.Lims>}) -> lxe.LIP(s, 1n+mm, LawsBase.wire_items.then(L.Lims, cur, r => LawsBase.wire_items(~L.Lims, ~FL.get_lims, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      lxe.lims_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), lxe.lims_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      lxe.lims_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(L.Lims, FL.get_lims(r1), r => LawsBase.wire_items(~L.Lims, ~FL.get_lims, k, r)), lxe.lims_items(k, FL.get_lims(r1), r1, {==}), lxe.lims_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def lxe.lims_items_of(k: Nat, +s: String) -> lxe.LIP(s, k, LawsBase.wire_items(~L.Lims, ~FL.get_lims, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      lxe.lims_items(mm, FL.get_lims(s), s, {==})

# what the list reader's answer says about its input s
def lxe.LLP(s: String, d: Wr.Dec<List<&2, L.Lims>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~L.Lims, ~Limits.sp_w_lims, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, L.Lims, xs)) == True{} : Bool} & {Limits.sp_fit_limss(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def lxe.lims_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, L.Lims>>, ip: lxe.LIP(s1, k, d)) -> lxe.LLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, L.Lims, xs)
      +w = LawsBase.wire_put_items(~L.Lims, ~Limits.sp_w_lims, xs, r)
      +es = Equal.trans(String, s, Wr.put_nat(k, s1), Wr.put_nat(k, w), en, Equal.cong(String, String, z => Wr.put_nat(k, z), s1, w, e1))
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ep = Equal.trans(String, Wr.put_nat(n, w), LawsBase.wire_dec(n, w), Wr.put_list(~L.Lims, ~Limits.sp_w_lims, xs, r), LAWireDec.wdec.nat(n, w), Equal.sym(String, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, xs, r), LawsBase.wire_dec(n, w), Wire.wire_list_spells_items(~L.Lims, ~Limits.sp_w_lims, xs, r)))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), Wr.put_list(~L.Lims, ~Limits.sp_w_lims, xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ep), (fl, e3))
    case Wr.Bad{}:
      Unit{}

def lxe.lims_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> lxe.LLP(s, LawsBase.wire_read_list.count(~L.Lims, ~FL.get_lims, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      lxe.lims_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~L.Lims, ~FL.get_lims, k, s1), lxe.lims_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only spelled lists of limits that fit
def lxe.limss(+s: String) -> lxe.LLP(s, Wr.get_list(~L.Lims, ~FL.get_lims, s)):
  %Equal.sym(Wr.Dec<List<&2, L.Lims>>, Wr.get_list(~L.Lims, ~FL.get_lims, s), LawsBase.wire_read_list(~L.Lims, ~FL.get_lims, s), Wire.wire_list_reads_items(~L.Lims, ~FL.get_lims, s)) : lxe.LLP(s, _)
  lxe.lims_count(s, Wr.get_nat(s), {==})

# what the item reader's answer says about its input s (k Nats)
def lxe.NIP(s: String, k: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_put_items(~Nat, ~Wr.put_nat, xs, r) : String} & ({List.length(&2, Nat, xs) == k : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def lxe.nat_at(+s: String, -d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> BX.bx.NP(s, d):
  %ed : BX.bx.NP(s, _)
  BX.bx.nat(s)

# an item before items read
def lxe.nat_cons(-s: String, +c: Nat, +r1: String, -k: Nat, d: Wr.Dec<List<&2, Nat>>, ih: lxe.NIP(r1, k, d), cp: BX.bx.NP(s, Wr.Got{c, r1})) -> lxe.NIP(s, 1n+k, LawsBase.wire_items.cons(Nat, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (lxe.tr(s, r1, LawsBase.wire_put_items(~Nat, ~Wr.put_nat, xs, r), z => Wr.put_nat(c, z), ec, e1), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, xs), k, e2), LBool.cb_and_intro(LawsBase.wire_fits(c), LawsBase.wire_nats_fit(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

# mm + 1 items, the first read from s as cur
def lxe.nat_items(mm: Nat, cur: Wr.Dec<Nat>, +s: String, er: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> lxe.NIP(s, 1n+mm, LawsBase.wire_items.then(Nat, cur, r => LawsBase.wire_items(~Nat, ~Wr.get_nat, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      lxe.nat_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), lxe.nat_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      lxe.nat_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(Nat, Wr.get_nat(r1), r => LawsBase.wire_items(~Nat, ~Wr.get_nat, k, r)), lxe.nat_items(k, Wr.get_nat(r1), r1, {==}), lxe.nat_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def lxe.nat_items_of(k: Nat, +s: String) -> lxe.NIP(s, k, LawsBase.wire_items(~Nat, ~Wr.get_nat, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      lxe.nat_items(mm, Wr.get_nat(s), s, {==})

# what the list reader's answer says about its input s
def lxe.NLP(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Nat, xs)) == True{} : Bool} & {LawsBase.wire_nats_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def lxe.nat_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ip: lxe.NIP(s1, k, d)) -> lxe.NLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, Nat, xs)
      +w = LawsBase.wire_put_items(~Nat, ~Wr.put_nat, xs, r)
      +es = Equal.trans(String, s, Wr.put_nat(k, s1), Wr.put_nat(k, w), en, Equal.cong(String, String, z => Wr.put_nat(k, z), s1, w, e1))
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ep = Equal.trans(String, Wr.put_nat(n, w), LawsBase.wire_dec(n, w), Wr.put_list(~Nat, ~Wr.put_nat, xs, r), LAWireDec.wdec.nat(n, w), Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), LawsBase.wire_dec(n, w), Wire.wire_list_spells_items(~Nat, ~Wr.put_nat, xs, r)))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), Wr.put_list(~Nat, ~Wr.put_nat, xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ep), (fl, e3))
    case Wr.Bad{}:
      Unit{}

def lxe.nat_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> lxe.NLP(s, LawsBase.wire_read_list.count(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      lxe.nat_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~Nat, ~Wr.get_nat, k, s1), lxe.nat_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only spelled lists of Nats that fit
def lxe.nats(+s: String) -> lxe.NLP(s, Wr.get_list(~Nat, ~Wr.get_nat, s)):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, s), LawsBase.wire_read_list(~Nat, ~Wr.get_nat, s), Wire.wire_list_reads_items(~Nat, ~Wr.get_nat, s)) : lxe.NLP(s, _)
  lxe.nat_count(s, Wr.get_nat(s), {==})

# the label and the used permille of a window fit the wire
def lxe.WF(w: L.Win) -> Type:
  match w:
    case L.Win{l, u}:
      {LawsBase.wire_fits(String.length(l)) == True{} : Bool} & {LawsBase.wire_fits(u) == True{} : Bool}

# what the window reader's answer says about its input s
def lxe.WP(s: String, d: Wr.Dec<L.Win>) -> Type:
  match d:
    case Wr.Got{w, r}:
      {s == Limits.sp_w_win(w, r) : String} & lxe.WF(w)
    case Wr.Bad{}:
      Unit

def lxe.win_u(-s: String, +l: String, -sk: String, pre: {s == Wr.put_str(l, sk) : String}, fl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool}, d: Wr.Dec<Nat>, np: BX.bx.NP(sk, d)) -> lxe.WP(s, FL.get_win.u(l, d)):
  match d:
    case Wr.Got{+u, +sn}:
      (e, fu) = np
      (lxe.tr(s, sk, Wr.put_nat(u, sn), z => Wr.put_str(l, z), pre, e), (fl, fu))
    case Wr.Bad{}:
      Unit{}

def lxe.win_l(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> lxe.WP(s, FL.get_win.l(d)):
  match d:
    case Wr.Got{+l, +sn}:
      +e2 = ed
      lxe.win_u(s, l, sn, Wire.wire_str_exact(s, l, sn, e2), Wire.wire_str_decoded_fits(s, l, sn, e2), Wr.get_nat(sn), BX.bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

# the window reader accepts only spelled windows that fit
def lxe.win(+s: String) -> lxe.WP(s, FL.get_win(s)):
  lxe.win_l(s, Wr.get_str(s), {==})

# what the item reader's answer says about its input s (k windows)
def lxe.WIP(s: String, k: Nat, d: Wr.Dec<List<&2, L.Win>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_put_items(~L.Win, ~Limits.sp_w_win, xs, r) : String} & ({List.length(&2, L.Win, xs) == k : Nat} & {Limits.sp_fit_wins(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def lxe.win_at(+s: String, -d: Wr.Dec<L.Win>, ed: {FL.get_win(s) == d : Wr.Dec<L.Win>}) -> lxe.WP(s, d):
  %ed : lxe.WP(s, _)
  lxe.win(s)

# an item before items read
def lxe.win_cons(-s: String, +c: L.Win, +r1: String, -k: Nat, d: Wr.Dec<List<&2, L.Win>>, ih: lxe.WIP(r1, k, d), cp: lxe.WP(s, Wr.Got{c, r1})) -> lxe.WIP(s, 1n+k, LawsBase.wire_items.cons(L.Win, c, d)):
  match c:
    case L.Win{+l, +u}:
      match d:
        case Wr.Got{+xs, +r}:
          (e1, (e2, e3)) = ih
          (ec, (fl, fu)) = cp
          (lxe.tr(s, r1, LawsBase.wire_put_items(~L.Win, ~Limits.sp_w_win, xs, r), z => Limits.sp_w_win(L.Win{l, u}, z), ec, e1), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, L.Win, xs), k, e2), LBool.cb_and_intro(LawsBase.wire_fits(String.length(l)), Bool.and(LawsBase.wire_fits(u), Limits.sp_fit_wins(xs)), fl, LBool.cb_and_intro(LawsBase.wire_fits(u), Limits.sp_fit_wins(xs), fu, e3))))
        case Wr.Bad{}:
          Unit{}

# mm + 1 items, the first read from s as cur
def lxe.win_items(mm: Nat, cur: Wr.Dec<L.Win>, +s: String, er: {FL.get_win(s) == cur : Wr.Dec<L.Win>}) -> lxe.WIP(s, 1n+mm, LawsBase.wire_items.then(L.Win, cur, r => LawsBase.wire_items(~L.Win, ~FL.get_win, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      lxe.win_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), lxe.win_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      lxe.win_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(L.Win, FL.get_win(r1), r => LawsBase.wire_items(~L.Win, ~FL.get_win, k, r)), lxe.win_items(k, FL.get_win(r1), r1, {==}), lxe.win_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def lxe.win_items_of(k: Nat, +s: String) -> lxe.WIP(s, k, LawsBase.wire_items(~L.Win, ~FL.get_win, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      lxe.win_items(mm, FL.get_win(s), s, {==})

# what the list reader's answer says about its input s
def lxe.WLP(s: String, d: Wr.Dec<List<&2, L.Win>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~L.Win, ~Limits.sp_w_win, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, L.Win, xs)) == True{} : Bool} & {Limits.sp_fit_wins(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def lxe.win_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, L.Win>>, ip: lxe.WIP(s1, k, d)) -> lxe.WLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, L.Win, xs)
      +w = LawsBase.wire_put_items(~L.Win, ~Limits.sp_w_win, xs, r)
      +es = Equal.trans(String, s, Wr.put_nat(k, s1), Wr.put_nat(k, w), en, Equal.cong(String, String, z => Wr.put_nat(k, z), s1, w, e1))
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ep = Equal.trans(String, Wr.put_nat(n, w), LawsBase.wire_dec(n, w), Wr.put_list(~L.Win, ~Limits.sp_w_win, xs, r), LAWireDec.wdec.nat(n, w), Equal.sym(String, Wr.put_list(~L.Win, ~Limits.sp_w_win, xs, r), LawsBase.wire_dec(n, w), Wire.wire_list_spells_items(~L.Win, ~Limits.sp_w_win, xs, r)))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), Wr.put_list(~L.Win, ~Limits.sp_w_win, xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ep), (fl, e3))
    case Wr.Bad{}:
      Unit{}

def lxe.win_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> lxe.WLP(s, LawsBase.wire_read_list.count(~L.Win, ~FL.get_win, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      lxe.win_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~L.Win, ~FL.get_win, k, s1), lxe.win_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only spelled lists of windows that fit
def lxe.wins(+s: String) -> lxe.WLP(s, Wr.get_list(~L.Win, ~FL.get_win, s)):
  %Equal.sym(Wr.Dec<List<&2, L.Win>>, Wr.get_list(~L.Win, ~FL.get_win, s), LawsBase.wire_read_list(~L.Win, ~FL.get_win, s), Wire.wire_list_reads_items(~L.Win, ~FL.get_win, s)) : lxe.WLP(s, _)
  lxe.win_count(s, Wr.get_nat(s), {==})

# what the string list reader's answer says about its input s
def lxe.SLP(s: String, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~String, ~Wr.put_str, xs, r) : String} & {LawsBase.wire_strs_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def lxe.strs_at(+s: String, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s) == d : Wr.Dec<List<&2, String>>}) -> lxe.SLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      +e2 = ed
      (Equal.trans(String, s, LawsBase.wire_spell_strs(xs, r), Wr.put_list(~String, ~Wr.put_str, xs, r), Wire.wire_strs_exact(s, xs, r, e2), Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, xs, r), LawsBase.wire_spell_strs(xs, r), Wire.wire_strs_spells(xs, r))), Wire.wire_strs_decoded_fit(s, xs, r, e2))
    case Wr.Bad{}:
      Unit{}

# the string list reader accepts only spelled lists of strings that fit
def lxe.strs(+s: String) -> lxe.SLP(s, Wr.get_list(~String, ~Wr.get_str, s)):
  lxe.strs_at(s, Wr.get_list(~String, ~Wr.get_str, s), {==})

# The request
# -----------

# what the request reader's answer says about its input s
def lxe.RP(s: String, d: Wr.Dec<FL.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Limits.sp_w_req(q, r) : String} & {Limits.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a fill, field by field (the last field first: a stage calls the next)
def lxe.fill_own(-s: String, +t: L.Toggle, +k: L.Run, +a: L.Auth, +set: L.Lims, +ps: List<&2, L.Lims>, -sk: String, pre: {s == Limits.sp_w_fill_head(t, k, a, Limits.sp_w_lims(set, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, ps, sk))) : String}, fset: {Limits.sp_fit_lims(set) == True{} : Bool}, fl: {LawsBase.wire_fits(List.length(&2, L.Lims, ps)) == True{} : Bool}, fps: {Limits.sp_fit_limss(ps) == True{} : Bool}, d: Wr.Dec<L.Lims>, np: lxe.LP(sk, d)) -> lxe.RP(s, FL.get_fill.own(t, k, a, set, ps, d)):
  match d:
    case Wr.Got{+own, +sn}:
      (e, fo) = np
      (lxe.tr(s, sk, Limits.sp_w_lims(own, sn), z => Limits.sp_w_fill_head(t, k, a, Limits.sp_w_lims(set, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, ps, z))), pre, e), LBool.cb_and_intro(Limits.sp_fit_lims(set), Bool.and(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), Bool.and(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own))), fset, LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), Bool.and(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own)), fl, LBool.cb_and_intro(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own), fps, fo))))
    case Wr.Bad{}:
      Unit{}

def lxe.fill_ps(-s: String, +t: L.Toggle, +k: L.Run, +a: L.Auth, +set: L.Lims, -sk: String, pre: {s == Limits.sp_w_fill_head(t, k, a, Limits.sp_w_lims(set, sk)) : String}, fset: {Limits.sp_fit_lims(set) == True{} : Bool}, d: Wr.Dec<List<&2, L.Lims>>, np: lxe.LLP(sk, d)) -> lxe.RP(s, FL.get_fill.ps(t, k, a, set, d)):
  match d:
    case Wr.Got{+ps, +sn}:
      (e, (fl, fps)) = np
      lxe.fill_own(s, t, k, a, set, ps, sn, lxe.tr(s, sk, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, ps, sn), z => Limits.sp_w_fill_head(t, k, a, Limits.sp_w_lims(set, z)), pre, e), fset, fl, fps, FL.get_lims(sn), lxe.lims(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.fill_set(-s: String, +t: L.Toggle, +k: L.Run, +a: L.Auth, -sk: String, pre: {s == Limits.sp_w_fill_head(t, k, a, sk) : String}, d: Wr.Dec<L.Lims>, np: lxe.LP(sk, d)) -> lxe.RP(s, FL.get_fill.set(t, k, a, d)):
  match d:
    case Wr.Got{+set, +sn}:
      (e, fset) = np
      lxe.fill_ps(s, t, k, a, set, sn, lxe.tr(s, sk, Limits.sp_w_lims(set, sn), z => Limits.sp_w_fill_head(t, k, a, z), pre, e), fset, Wr.get_list(~L.Lims, ~FL.get_lims, sn), lxe.limss(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.fill_a(-s: String, +t: L.Toggle, +k: L.Run, -sk: String, pre: {s == Wr.put_nat(0n, Wr.put_bool(Limits.sp_on(t), Wr.put_nat(Limits.sp_kind_tag(k), sk))) : String}, d: Wr.Dec<L.Auth>, np: lxe.AP(sk, d)) -> lxe.RP(s, FL.get_fill.a(t, k, d)):
  match d:
    case Wr.Got{+a, +sn}:
      lxe.fill_set(s, t, k, a, sn, lxe.tr(s, sk, Wr.put_nat(Limits.sp_auth_tag(a), sn), z => Wr.put_nat(0n, Wr.put_bool(Limits.sp_on(t), Wr.put_nat(Limits.sp_kind_tag(k), z))), pre, np), FL.get_lims(sn), lxe.lims(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.fill_k(-s: String, +t: L.Toggle, -sk: String, pre: {s == Wr.put_nat(0n, Wr.put_bool(Limits.sp_on(t), sk)) : String}, d: Wr.Dec<L.Run>, np: lxe.KP(sk, d)) -> lxe.RP(s, FL.get_fill.k(t, d)):
  match d:
    case Wr.Got{+k, +sn}:
      lxe.fill_a(s, t, k, sn, lxe.tr(s, sk, Wr.put_nat(Limits.sp_kind_tag(k), sn), z => Wr.put_nat(0n, Wr.put_bool(Limits.sp_on(t), z)), pre, np), FL.get_auth(sn), lxe.auth(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.fill_t(-s: String, -sk: String, pre: {s == Wr.put_nat(0n, sk) : String}, d: Wr.Dec<L.Toggle>, np: lxe.TP(sk, d)) -> lxe.RP(s, FL.get_fill.t(d)):
  match d:
    case Wr.Got{+t, +sn}:
      lxe.fill_k(s, t, sn, lxe.tr(s, sk, Wr.put_bool(Limits.sp_on(t), sn), z => Wr.put_nat(0n, z), pre, np), FL.get_kind(sn), lxe.kind(sn))
    case Wr.Bad{}:
      Unit{}

# a profile
def lxe.profile_a(-s: String, +k: L.Run, -sk: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(Limits.sp_kind_tag(k), sk)) : String}, d: Wr.Dec<L.Auth>, np: lxe.AP(sk, d)) -> lxe.RP(s, FL.get_profile.a(k, d)):
  match d:
    case Wr.Got{+a, +sn}:
      (lxe.tr(s, sk, Wr.put_nat(Limits.sp_auth_tag(a), sn), z => Wr.put_nat(1n, Wr.put_nat(Limits.sp_kind_tag(k), z)), pre, np), {==})
    case Wr.Bad{}:
      Unit{}

def lxe.profile_k(-s: String, -sk: String, pre: {s == Wr.put_nat(1n, sk) : String}, d: Wr.Dec<L.Run>, np: lxe.KP(sk, d)) -> lxe.RP(s, FL.get_profile.k(d)):
  match d:
    case Wr.Got{+k, +sn}:
      lxe.profile_a(s, k, sn, lxe.tr(s, sk, Wr.put_nat(Limits.sp_kind_tag(k), sn), z => Wr.put_nat(1n, z), pre, np), FL.get_auth(sn), lxe.auth(sn))
    case Wr.Bad{}:
      Unit{}

# a preset
def lxe.preset_a(-s: String, +c: L.Scale, +k: L.Run, -sk: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), Wr.put_nat(Limits.sp_kind_tag(k), sk))) : String}, d: Wr.Dec<L.Auth>, np: lxe.AP(sk, d)) -> lxe.RP(s, FL.get_preset.a(c, k, d)):
  match d:
    case Wr.Got{+a, +sn}:
      (lxe.tr(s, sk, Wr.put_nat(Limits.sp_auth_tag(a), sn), z => Wr.put_nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), Wr.put_nat(Limits.sp_kind_tag(k), z))), pre, np), {==})
    case Wr.Bad{}:
      Unit{}

def lxe.preset_k(-s: String, +c: L.Scale, -sk: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), sk)) : String}, d: Wr.Dec<L.Run>, np: lxe.KP(sk, d)) -> lxe.RP(s, FL.get_preset.k(c, d)):
  match d:
    case Wr.Got{+k, +sn}:
      lxe.preset_a(s, c, k, sn, lxe.tr(s, sk, Wr.put_nat(Limits.sp_kind_tag(k), sn), z => Wr.put_nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), z)), pre, np), FL.get_auth(sn), lxe.auth(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.preset_c(-s: String, -sk: String, pre: {s == Wr.put_nat(2n, sk) : String}, d: Wr.Dec<L.Scale>, np: lxe.SP(sk, d)) -> lxe.RP(s, FL.get_preset.c(d)):
  match d:
    case Wr.Got{+c, +sn}:
      lxe.preset_k(s, c, sn, lxe.tr(s, sk, Wr.put_nat(Limits.sp_scale_tag(c), sn), z => Wr.put_nat(2n, z), pre, np), FL.get_kind(sn), lxe.kind(sn))
    case Wr.Bad{}:
      Unit{}

# a plan's wrap-up line
def lxe.wraps_r(-s: String, +us: List<&2, Nat>, -sk: String, pre: {s == Wr.put_nat(3n, Wr.put_list(~Nat, ~Wr.put_nat, us, sk)) : String}, fl: {LawsBase.wire_fits(List.length(&2, Nat, us)) == True{} : Bool}, fus: {LawsBase.wire_nats_fit(us) == True{} : Bool}, d: Wr.Dec<Nat>, np: BX.bx.NP(sk, d)) -> lxe.RP(s, FL.get_wraps.r(us, d)):
  match d:
    case Wr.Got{+r, +sn}:
      (e, fr) = np
      (lxe.tr(s, sk, Wr.put_nat(r, sn), z => Wr.put_nat(3n, Wr.put_list(~Nat, ~Wr.put_nat, us, z)), pre, e), LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, Nat, us)), Bool.and(LawsBase.wire_nats_fit(us), LawsBase.wire_fits(r)), fl, LBool.cb_and_intro(LawsBase.wire_nats_fit(us), LawsBase.wire_fits(r), fus, fr)))
    case Wr.Bad{}:
      Unit{}

def lxe.wraps_us(-s: String, -sk: String, pre: {s == Wr.put_nat(3n, sk) : String}, d: Wr.Dec<List<&2, Nat>>, np: lxe.NLP(sk, d)) -> lxe.RP(s, FL.get_wraps.us(d)):
  match d:
    case Wr.Got{+us, +sn}:
      (e, (fl, fus)) = np
      lxe.wraps_r(s, us, sn, lxe.tr(s, sk, Wr.put_list(~Nat, ~Wr.put_nat, us, sn), z => Wr.put_nat(3n, z), pre, e), fl, fus, Wr.get_nat(sn), BX.bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

# a plan notice
def lxe.notice_told(-s: String, +ws: List<&2, L.Win>, +r: Nat, -sk: String, pre: {s == Wr.put_nat(4n, Wr.put_list(~L.Win, ~Limits.sp_w_win, ws, Wr.put_nat(r, sk))) : String}, fl: {LawsBase.wire_fits(List.length(&2, L.Win, ws)) == True{} : Bool}, fw: {Limits.sp_fit_wins(ws) == True{} : Bool}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, np: lxe.SLP(sk, d)) -> lxe.RP(s, FL.get_notice.told(ws, r, d)):
  match d:
    case Wr.Got{+told, +sn}:
      (e, ft) = np
      (lxe.tr(s, sk, Wr.put_list(~String, ~Wr.put_str, told, sn), z => Wr.put_nat(4n, Wr.put_list(~L.Win, ~Limits.sp_w_win, ws, Wr.put_nat(r, z))), pre, e), LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, L.Win, ws)), Bool.and(Limits.sp_fit_wins(ws), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_strs_fit(told))), fl, LBool.cb_and_intro(Limits.sp_fit_wins(ws), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_strs_fit(told)), fw, LBool.cb_and_intro(LawsBase.wire_fits(r), LawsBase.wire_strs_fit(told), fr, ft))))
    case Wr.Bad{}:
      Unit{}

def lxe.notice_r(-s: String, +ws: List<&2, L.Win>, -sk: String, pre: {s == Wr.put_nat(4n, Wr.put_list(~L.Win, ~Limits.sp_w_win, ws, sk)) : String}, fl: {LawsBase.wire_fits(List.length(&2, L.Win, ws)) == True{} : Bool}, fw: {Limits.sp_fit_wins(ws) == True{} : Bool}, d: Wr.Dec<Nat>, np: BX.bx.NP(sk, d)) -> lxe.RP(s, FL.get_notice.r(ws, d)):
  match d:
    case Wr.Got{+r, +sn}:
      (e, fr) = np
      lxe.notice_told(s, ws, r, sn, lxe.tr(s, sk, Wr.put_nat(r, sn), z => Wr.put_nat(4n, Wr.put_list(~L.Win, ~Limits.sp_w_win, ws, z)), pre, e), fl, fw, fr, Wr.get_list(~String, ~Wr.get_str, sn), lxe.strs(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.notice_ws(-s: String, -sk: String, pre: {s == Wr.put_nat(4n, sk) : String}, d: Wr.Dec<List<&2, L.Win>>, np: lxe.WLP(sk, d)) -> lxe.RP(s, FL.get_notice.ws(d)):
  match d:
    case Wr.Got{+ws, +sn}:
      (e, (fl, fw)) = np
      lxe.notice_r(s, ws, sn, lxe.tr(s, sk, Wr.put_list(~L.Win, ~Limits.sp_w_win, ws, sn), z => Wr.put_nat(4n, z), pre, e), fl, fw, Wr.get_nat(sn), BX.bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

# a floor
def lxe.floor_keep(-s: String, +l: L.Lims, +c: B.Ask, -sk: String, pre: {s == Wr.put_nat(5n, Limits.sp_w_lims(l, Budget.sp_w_ask(c, sk))) : String}, fl: {Limits.sp_fit_lims(l) == True{} : Bool}, fc: {Budget.sp_fit_ask(c) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: BX.bx.KP(sk, d)) -> lxe.RP(s, FL.get_floor.keep(l, c, d)):
  match d:
    case Wr.Got{+keep, +sn}:
      (e, fk) = np
      (lxe.tr(s, sk, Budget.sp_w_ask(keep, sn), z => Wr.put_nat(5n, Limits.sp_w_lims(l, Budget.sp_w_ask(c, z))), pre, e), LBool.cb_and_intro(Limits.sp_fit_lims(l), Bool.and(Budget.sp_fit_ask(c), Budget.sp_fit_ask(keep)), fl, LBool.cb_and_intro(Budget.sp_fit_ask(c), Budget.sp_fit_ask(keep), fc, fk)))
    case Wr.Bad{}:
      Unit{}

def lxe.floor_c(-s: String, +l: L.Lims, -sk: String, pre: {s == Wr.put_nat(5n, Limits.sp_w_lims(l, sk)) : String}, fl: {Limits.sp_fit_lims(l) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: BX.bx.KP(sk, d)) -> lxe.RP(s, FL.get_floor.c(l, d)):
  match d:
    case Wr.Got{+c, +sn}:
      (e, fc) = np
      lxe.floor_keep(s, l, c, sn, lxe.tr(s, sk, Budget.sp_w_ask(c, sn), z => Wr.put_nat(5n, Limits.sp_w_lims(l, z)), pre, e), fl, fc, FB.get_ask(sn), BX.bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.floor_l(-s: String, -sk: String, pre: {s == Wr.put_nat(5n, sk) : String}, d: Wr.Dec<L.Lims>, np: lxe.LP(sk, d)) -> lxe.RP(s, FL.get_floor.l(d)):
  match d:
    case Wr.Got{+l, +sn}:
      (e, fl) = np
      lxe.floor_c(s, l, sn, lxe.tr(s, sk, Limits.sp_w_lims(l, sn), z => Wr.put_nat(5n, z), pre, e), fl, FB.get_ask(sn), BX.bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

# a renewal
def lxe.renew_a(-s: String, +l: L.Lims, +mark: B.Amt, +now: Nat, -sk: String, pre: {s == Wr.put_nat(6n, Limits.sp_w_lims(l, Budget.sp_w_amt(mark, Wr.put_nat(now, sk)))) : String}, fl: {Limits.sp_fit_lims(l) == True{} : Bool}, fm: {Budget.sp_fit_amt(mark) == True{} : Bool}, fn: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<B.Acct>, np: BX.bx.CP(sk, d)) -> lxe.RP(s, FL.get_renew.a(l, mark, now, d)):
  match d:
    case Wr.Got{+a, +sn}:
      (e, fa) = np
      (lxe.tr(s, sk, Budget.sp_w_acct(a, sn), z => Wr.put_nat(6n, Limits.sp_w_lims(l, Budget.sp_w_amt(mark, Wr.put_nat(now, z)))), pre, e), LBool.cb_and_intro(Limits.sp_fit_lims(l), Bool.and(Budget.sp_fit_amt(mark), Bool.and(LawsBase.wire_fits(now), Budget.sp_fit_acct(a))), fl, LBool.cb_and_intro(Budget.sp_fit_amt(mark), Bool.and(LawsBase.wire_fits(now), Budget.sp_fit_acct(a)), fm, LBool.cb_and_intro(LawsBase.wire_fits(now), Budget.sp_fit_acct(a), fn, fa))))
    case Wr.Bad{}:
      Unit{}

def lxe.renew_now(-s: String, +l: L.Lims, +mark: B.Amt, -sk: String, pre: {s == Wr.put_nat(6n, Limits.sp_w_lims(l, Budget.sp_w_amt(mark, sk))) : String}, fl: {Limits.sp_fit_lims(l) == True{} : Bool}, fm: {Budget.sp_fit_amt(mark) == True{} : Bool}, d: Wr.Dec<Nat>, np: BX.bx.NP(sk, d)) -> lxe.RP(s, FL.get_renew.now(l, mark, d)):
  match d:
    case Wr.Got{+now, +sn}:
      (e, fn) = np
      lxe.renew_a(s, l, mark, now, sn, lxe.tr(s, sk, Wr.put_nat(now, sn), z => Wr.put_nat(6n, Limits.sp_w_lims(l, Budget.sp_w_amt(mark, z))), pre, e), fl, fm, fn, FB.get_acct(sn), BX.bx.acct(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.renew_mark(-s: String, +l: L.Lims, -sk: String, pre: {s == Wr.put_nat(6n, Limits.sp_w_lims(l, sk)) : String}, fl: {Limits.sp_fit_lims(l) == True{} : Bool}, d: Wr.Dec<B.Amt>, np: BX.bx.AP(sk, d)) -> lxe.RP(s, FL.get_renew.mark(l, d)):
  match d:
    case Wr.Got{+mark, +sn}:
      (e, fm) = np
      lxe.renew_now(s, l, mark, sn, lxe.tr(s, sk, Budget.sp_w_amt(mark, sn), z => Wr.put_nat(6n, Limits.sp_w_lims(l, z)), pre, e), fl, fm, Wr.get_nat(sn), BX.bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

def lxe.renew_l(-s: String, -sk: String, pre: {s == Wr.put_nat(6n, sk) : String}, d: Wr.Dec<L.Lims>, np: lxe.LP(sk, d)) -> lxe.RP(s, FL.get_renew.l(d)):
  match d:
    case Wr.Got{+l, +sn}:
      (e, fl) = np
      lxe.renew_mark(s, l, sn, lxe.tr(s, sk, Limits.sp_w_lims(l, sn), z => Wr.put_nat(6n, z), pre, e), fl, FB.get_amt(sn), BX.bx.amt(sn))
    case Wr.Bad{}:
      Unit{}

# a message's prefix
def lxe.prefix_ns(-s: String, +text: String, -sk: String, pre: {s == Wr.put_nat(7n, Wr.put_str(text, sk)) : String}, ft: {LawsBase.wire_fits(String.length(text)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, np: lxe.SLP(sk, d)) -> lxe.RP(s, FL.get_prefix.ns(text, d)):
  match d:
    case Wr.Got{+ns, +sn}:
      (e, fns) = np
      (lxe.tr(s, sk, Wr.put_list(~String, ~Wr.put_str, ns, sn), z => Wr.put_nat(7n, Wr.put_str(text, z)), pre, e), LBool.cb_and_intro(LawsBase.wire_fits(String.length(text)), LawsBase.wire_strs_fit(ns), ft, fns))
    case Wr.Bad{}:
      Unit{}

def lxe.prefix_text(+sk: String, -s: String, pre: {s == Wr.put_nat(7n, sk) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(sk) == d : Wr.Dec<String>}) -> lxe.RP(s, FL.get_prefix.text(d)):
  match d:
    case Wr.Got{+text, +sn}:
      +e2 = ed
      lxe.prefix_ns(s, text, sn, lxe.tr(s, sk, Wr.put_str(text, sn), z => Wr.put_nat(7n, z), pre, Wire.wire_str_exact(sk, text, sn, e2)), Wire.wire_str_decoded_fits(sk, text, sn, e2), Wr.get_list(~String, ~Wr.get_str, sn), lxe.strs(sn))
    case Wr.Bad{}:
      Unit{}

# the request of tag n
def lxe.of(n: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> lxe.RP(s, FL.get_req.of(n, s1)):
  match n:
    case 0n:
      lxe.fill_t(s, s1, pre, FL.get_toggle(s1), lxe.tog(s1))
    case 1n:
      lxe.profile_k(s, s1, pre, FL.get_kind(s1), lxe.kind(s1))
    case 2n:
      lxe.preset_c(s, s1, pre, FL.get_scale(s1), lxe.scale(s1))
    case 3n:
      lxe.wraps_us(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), lxe.nats(s1))
    case 4n:
      lxe.notice_ws(s, s1, pre, Wr.get_list(~L.Win, ~FL.get_win, s1), lxe.wins(s1))
    case 5n:
      lxe.floor_l(s, s1, pre, FL.get_lims(s1), lxe.lims(s1))
    case 6n:
      lxe.renew_l(s, s1, pre, FL.get_lims(s1), lxe.lims(s1))
    case 7n:
      lxe.prefix_text(s1, s, pre, Wr.get_str(s1), {==})
    case 8n+p:
      Unit{}

def lxe.tag(-s: String, d: Wr.Dec<Nat>, np: BX.bx.NP(s, d)) -> lxe.RP(s, FL.get_req.n(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = np
      lxe.of(n, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the request reader accepts only spelled requests that fit
def lxe.req(+s: String) -> lxe.RP(s, FL.get_req(s)):
  lxe.tag(s, Wr.get_nat(s), BX.bx.nat(s))

# The entry
# ---------

def lxe.top(-s: String, d: Wr.Dec<FL.Req>, rp: lxe.RP(s, d), ok: {LawsBase.wire_opens_err(FL.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FL.Req, v => {s == Limits.sp_w_req(v, "") : String} & {Limits.sp_fit_req(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FL.Req, v2 => {s == Limits.sp_w_req(v2, "") : String} & {Limits.sp_fit_req(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FL.Req, v2 => {s == Limits.sp_w_req(v2, "") : String} & {Limits.sp_fit_req(v2) == True{} : Bool}>, ok)

def Limits.limits_entry_exact(s, ok):
  lxe.top(s, FL.get_req(s), lxe.req(s), ok)
