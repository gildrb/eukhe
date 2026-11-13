# eukhe: lemmas of the exactness proofs of the budget entry
# (bend/ffi_budget.bend), used by area budget and area budget_share: each
# decoder answers a value only for an input that is its spelling, every
# number and count within the wire (bx.*: a predicate per decoder answer,
# carried field by field with wire_nat_exact, wire_nat_decoded_fits and the
# generic list laws)

import Base
import ../../../bend/budget.bend as B
import ../../../bend/ffi_budget.bend as FBg
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/budget.bend as Budget
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../../wire/wire_list_spells_items.bend as PWireListSpellsItems
import ../../wire/base/dec.bend as LAWireDec
import ../../base/bool.bend as LBool

# Numbers
# -------

# what a Nat reader's answer says about its input s
def bx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def bx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> bx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

# the Nat reader accepts only spelled numbers that fit
def bx.nat(+s: String) -> bx.NP(s, Wr.get_nat(s)):
  bx.nat.at(s, Wr.get_nat(s), {==})

# Amounts, asks, holds, phases
# ----------------------------

# what an amount reader's answer says about its input s
def bx.AP(s: String, d: Wr.Dec<B.Amt>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Budget.sp_w_amt(x, r) : String} & {Budget.sp_fit_amt(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def bx.amt_3(-s: String, +c: Nat, +k: Nat, +n: Nat, +sk: String, pre: {s == Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, sk))) : String}, f0_c: {LawsBase.wire_fits(c) == True{} : Bool}, f0_k: {LawsBase.wire_fits(k) == True{} : Bool}, f0_n: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.AP(s, FBg.get_amt.r(c, k, n, d)):
  match d:
    case Wr.Got{+q, +sn}:
      (e, f0_q) = np
      (Equal.trans(String, s, Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, sk))), Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, Wr.put_nat(q, sn)))), pre, Equal.cong(String, String, z => Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, z))), sk, Wr.put_nat(q, sn), e)), LBool.cb_and_intro(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(q))), f0_c, LBool.cb_and_intro(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(q)), f0_k, LBool.cb_and_intro(LawsBase.wire_fits(n), LawsBase.wire_fits(q), f0_n, f0_q))))
    case Wr.Bad{}:
      Unit{}

def bx.amt_2(-s: String, +c: Nat, +k: Nat, +sk: String, pre: {s == Wr.put_nat(c, Wr.put_nat(k, sk)) : String}, f0_c: {LawsBase.wire_fits(c) == True{} : Bool}, f0_k: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.AP(s, FBg.get_amt.n(c, k, d)):
  match d:
    case Wr.Got{+n, +sn}:
      (e, f0_n) = np
      bx.amt_3(s, c, k, n, sn, Equal.trans(String, s, Wr.put_nat(c, Wr.put_nat(k, sk)), Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, sn))), pre, Equal.cong(String, String, z => Wr.put_nat(c, Wr.put_nat(k, z)), sk, Wr.put_nat(n, sn), e)), f0_c, f0_k, f0_n, Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

def bx.amt_1(-s: String, +c: Nat, +sk: String, pre: {s == Wr.put_nat(c, sk) : String}, f0_c: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.AP(s, FBg.get_amt.k(c, d)):
  match d:
    case Wr.Got{+k, +sn}:
      (e, f0_k) = np
      bx.amt_2(s, c, k, sn, Equal.trans(String, s, Wr.put_nat(c, sk), Wr.put_nat(c, Wr.put_nat(k, sn)), pre, Equal.cong(String, String, z => Wr.put_nat(c, z), sk, Wr.put_nat(k, sn), e)), f0_c, f0_k, Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

def bx.amt_0(-s: String, +sk: String, pre: {s == sk : String}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.AP(s, FBg.get_amt.c(d)):
  match d:
    case Wr.Got{+c, +sn}:
      (e, f0_c) = np
      bx.amt_1(s, c, sn, Equal.trans(String, s, sk, Wr.put_nat(c, sn), pre, Equal.cong(String, String, z => z, sk, Wr.put_nat(c, sn), e)), f0_c, Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

# the amount reader accepts only spelled amounts that fit
def bx.amt(+s: String) -> bx.AP(s, FBg.get_amt(s)):
  bx.amt_0(s, s, {==}, Wr.get_nat(s), bx.nat(s))

# what an ask reader's answer says about its input s
def bx.KP(s: String, d: Wr.Dec<B.Ask>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Budget.sp_w_ask(x, r) : String} & {Budget.sp_fit_ask(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def bx.ask_1(-s: String, +a: B.Amt, +sk: String, pre: {s == Budget.sp_w_amt(a, sk) : String}, f0_a: {Budget.sp_fit_amt(a) == True{} : Bool}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.KP(s, FBg.get_ask.ms(a, d)):
  match d:
    case Wr.Got{+m, +sn}:
      (e, f0_m) = np
      (Equal.trans(String, s, Budget.sp_w_amt(a, sk), Budget.sp_w_amt(a, Wr.put_nat(m, sn)), pre, Equal.cong(String, String, z => Budget.sp_w_amt(a, z), sk, Wr.put_nat(m, sn), e)), LBool.cb_and_intro(Budget.sp_fit_amt(a), LawsBase.wire_fits(m), f0_a, f0_m))
    case Wr.Bad{}:
      Unit{}

def bx.ask_0(-s: String, +sk: String, pre: {s == sk : String}, d: Wr.Dec<B.Amt>, np: bx.AP(sk, d)) -> bx.KP(s, FBg.get_ask.amt(d)):
  match d:
    case Wr.Got{+a, +sn}:
      (e, f0_a) = np
      bx.ask_1(s, a, sn, Equal.trans(String, s, sk, Budget.sp_w_amt(a, sn), pre, Equal.cong(String, String, z => z, sk, Budget.sp_w_amt(a, sn), e)), f0_a, Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

# the ask reader accepts only spelled asks that fit
def bx.ask(+s: String) -> bx.KP(s, FBg.get_ask(s)):
  bx.ask_0(s, s, {==}, FBg.get_amt(s), bx.amt(s))

# the numbers of a hold fit the wire
def bx.HF(h: B.Hold) -> Type:
  match h:
    case B.Hold{i, x}:
      {LawsBase.wire_fits(i) == True{} : Bool} & {Budget.sp_fit_amt(x) == True{} : Bool}

# what a hold reader's answer says about its input s
def bx.HP(s: String, d: Wr.Dec<B.Hold>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Budget.sp_w_hold(x, r) : String} & bx.HF(x)
    case Wr.Bad{}:
      Unit

def bx.hold_1(-s: String, +i: Nat, +sk: String, pre: {s == Wr.put_nat(i, sk) : String}, f0_i: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<B.Amt>, np: bx.AP(sk, d)) -> bx.HP(s, FBg.get_hold.amt(i, d)):
  match d:
    case Wr.Got{+x, +sn}:
      (e, f0_x) = np
      (Equal.trans(String, s, Wr.put_nat(i, sk), Wr.put_nat(i, Budget.sp_w_amt(x, sn)), pre, Equal.cong(String, String, z => Wr.put_nat(i, z), sk, Budget.sp_w_amt(x, sn), e)), (f0_i, f0_x))
    case Wr.Bad{}:
      Unit{}

def bx.hold_0(-s: String, +sk: String, pre: {s == sk : String}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.HP(s, FBg.get_hold.id(d)):
  match d:
    case Wr.Got{+i, +sn}:
      (e, f0_i) = np
      bx.hold_1(s, i, sn, Equal.trans(String, s, sk, Wr.put_nat(i, sn), pre, Equal.cong(String, String, z => z, sk, Wr.put_nat(i, sn), e)), f0_i, FBg.get_amt(sn), bx.amt(sn))
    case Wr.Bad{}:
      Unit{}

# the hold reader accepts only spelled holds that fit
def bx.hold(+s: String) -> bx.HP(s, FBg.get_hold(s)):
  bx.hold_0(s, s, {==}, Wr.get_nat(s), bx.nat(s))

# what a phase reader's answer says about its input s
def bx.PP(s: String, d: Wr.Dec<B.Phase>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == Wr.put_nat(Budget.sp_phase_tag(p), r) : String}
    case Wr.Bad{}:
      Unit

# the phase of tag n
def bx.phase_of(n: Nat, -s: String, +s1: String, e: {s == Wr.put_nat(n, s1) : String}) -> bx.PP(s, FBg.get_phase.of(n, s1)):
  match n:
    case 0n:
      e
    case 1n+a:
      match a:
        case 0n:
          e
        case 1n+b:
          match b:
            case 0n:
              e
            case 1n+c:
              Unit{}

def bx.phase_tag(-s: String, d: Wr.Dec<Nat>, np: bx.NP(s, d)) -> bx.PP(s, FBg.get_phase.tag(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = np
      bx.phase_of(n, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the phase reader accepts only spelled phases
def bx.phase(+s: String) -> bx.PP(s, FBg.get_phase(s)):
  bx.phase_tag(s, Wr.get_nat(s), bx.nat(s))

# Lists: asks and holds
# ---------------------

# what the item reader's answer says about its input s (k items)
def bx.AIP(s: String, k: Nat, d: Wr.Dec<List<&2, B.Ask>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, r) : String} & ({List.length(&2, B.Ask, xs) == k : Nat} & {Budget.sp_fit_asks(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def bx.ask_at(+s: String, -d: Wr.Dec<B.Ask>, ed: {FBg.get_ask(s) == d : Wr.Dec<B.Ask>}) -> bx.KP(s, d):
  %ed : bx.KP(s, _)
  bx.ask(s)

# an item before items read
def bx.ask_cons(-s: String, +c: B.Ask, +r1: String, -k: Nat, d: Wr.Dec<List<&2, B.Ask>>, ih: bx.AIP(r1, k, d), cp: bx.KP(s, Wr.Got{c, r1})) -> bx.AIP(s, 1n+k, LawsBase.wire_items.cons(B.Ask, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (Equal.trans(String, s, Budget.sp_w_ask(c, r1), Budget.sp_w_ask(c, LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, r)), ec, Equal.cong(String, String, z => Budget.sp_w_ask(c, z), r1, LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, r), e1)), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, B.Ask, xs), k, e2), LBool.cb_and_intro(Budget.sp_fit_ask(c), Budget.sp_fit_asks(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

# mm + 1 items, the first read from s as cur
def bx.ask_items(mm: Nat, cur: Wr.Dec<B.Ask>, +s: String, er: {FBg.get_ask(s) == cur : Wr.Dec<B.Ask>}) -> bx.AIP(s, 1n+mm, LawsBase.wire_items.then(B.Ask, cur, r => LawsBase.wire_items(~B.Ask, ~FBg.get_ask, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      bx.ask_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), bx.ask_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      bx.ask_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(B.Ask, FBg.get_ask(r1), r => LawsBase.wire_items(~B.Ask, ~FBg.get_ask, k, r)), bx.ask_items(k, FBg.get_ask(r1), r1, {==}), bx.ask_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def bx.ask_items_of(k: Nat, +s: String) -> bx.AIP(s, k, LawsBase.wire_items(~B.Ask, ~FBg.get_ask, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      bx.ask_items(mm, FBg.get_ask(s), s, {==})

# what the list reader's answer says about its input s
def bx.LP(s: String, d: Wr.Dec<List<&2, B.Ask>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~B.Ask, ~Budget.sp_w_ask, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, B.Ask, xs)) == True{} : Bool} & {Budget.sp_fit_asks(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def bx.ask_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, B.Ask>>, ip: bx.AIP(s1, k, d)) -> bx.LP(s, d):
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

def bx.ask_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> bx.LP(s, LawsBase.wire_read_list.count(~B.Ask, ~FBg.get_ask, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      bx.ask_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~B.Ask, ~FBg.get_ask, k, s1), bx.ask_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only spelled lists that fit
def bx.asks(+s: String) -> bx.LP(s, Wr.get_list(~B.Ask, ~FBg.get_ask, s)):
  %Equal.sym(Wr.Dec<List<&2, B.Ask>>, Wr.get_list(~B.Ask, ~FBg.get_ask, s), LawsBase.wire_read_list(~B.Ask, ~FBg.get_ask, s), Wire.wire_list_reads_items(~B.Ask, ~FBg.get_ask, s)) : bx.LP(s, _)
  bx.ask_count(s, Wr.get_nat(s), {==})

# what the item reader's answer says about its input s (k items)
def bx.HIP(s: String, k: Nat, d: Wr.Dec<List<&2, B.Hold>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, xs, r) : String} & ({List.length(&2, B.Hold, xs) == k : Nat} & {Budget.sp_fit_holds(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def bx.hold_at(+s: String, -d: Wr.Dec<B.Hold>, ed: {FBg.get_hold(s) == d : Wr.Dec<B.Hold>}) -> bx.HP(s, d):
  %ed : bx.HP(s, _)
  bx.hold(s)

# an item before items read
def bx.hold_cons(-s: String, +c: B.Hold, +r1: String, -k: Nat, d: Wr.Dec<List<&2, B.Hold>>, ih: bx.HIP(r1, k, d), cp: bx.HP(s, Wr.Got{c, r1})) -> bx.HIP(s, 1n+k, LawsBase.wire_items.cons(B.Hold, c, d)):
  match c:
    case B.Hold{+i, +x}:
      match d:
        case Wr.Got{+xs, +r}:
          (e1, (e2, e3)) = ih
          (ec, (fi, fx)) = cp
          (Equal.trans(String, s, Budget.sp_w_hold(B.Hold{i, x}, r1), Budget.sp_w_hold(B.Hold{i, x}, LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, xs, r)), ec, Equal.cong(String, String, z => Budget.sp_w_hold(B.Hold{i, x}, z), r1, LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, xs, r), e1)), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, B.Hold, xs), k, e2), LBool.cb_and_intro(LawsBase.wire_fits(i), Bool.and(Budget.sp_fit_amt(x), Budget.sp_fit_holds(xs)), fi, LBool.cb_and_intro(Budget.sp_fit_amt(x), Budget.sp_fit_holds(xs), fx, e3))))
        case Wr.Bad{}:
          Unit{}

# mm + 1 items, the first read from s as cur
def bx.hold_items(mm: Nat, cur: Wr.Dec<B.Hold>, +s: String, er: {FBg.get_hold(s) == cur : Wr.Dec<B.Hold>}) -> bx.HIP(s, 1n+mm, LawsBase.wire_items.then(B.Hold, cur, r => LawsBase.wire_items(~B.Hold, ~FBg.get_hold, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      bx.hold_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), bx.hold_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      bx.hold_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(B.Hold, FBg.get_hold(r1), r => LawsBase.wire_items(~B.Hold, ~FBg.get_hold, k, r)), bx.hold_items(k, FBg.get_hold(r1), r1, {==}), bx.hold_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def bx.hold_items_of(k: Nat, +s: String) -> bx.HIP(s, k, LawsBase.wire_items(~B.Hold, ~FBg.get_hold, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      bx.hold_items(mm, FBg.get_hold(s), s, {==})

# what the list reader's answer says about its input s
def bx.HLP(s: String, d: Wr.Dec<List<&2, B.Hold>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~B.Hold, ~Budget.sp_w_hold, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, B.Hold, xs)) == True{} : Bool} & {Budget.sp_fit_holds(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def bx.hold_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, B.Hold>>, ip: bx.HIP(s1, k, d)) -> bx.HLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, B.Hold, xs)
      +w = LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, xs, r)
      +es = Equal.trans(String, s, Wr.put_nat(k, s1), Wr.put_nat(k, w), en, Equal.cong(String, String, z => Wr.put_nat(k, z), s1, w, e1))
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ep = Equal.trans(String, Wr.put_nat(n, w), LawsBase.wire_dec(n, w), Wr.put_list(~B.Hold, ~Budget.sp_w_hold, xs, r), LAWireDec.wdec.nat(n, w), Equal.sym(String, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, xs, r), LawsBase.wire_dec(n, w), Wire.wire_list_spells_items(~B.Hold, ~Budget.sp_w_hold, xs, r)))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), Wr.put_list(~B.Hold, ~Budget.sp_w_hold, xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ep), (fl, e3))
    case Wr.Bad{}:
      Unit{}

def bx.hold_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> bx.HLP(s, LawsBase.wire_read_list.count(~B.Hold, ~FBg.get_hold, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      bx.hold_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~B.Hold, ~FBg.get_hold, k, s1), bx.hold_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only spelled lists that fit
def bx.holds(+s: String) -> bx.HLP(s, Wr.get_list(~B.Hold, ~FBg.get_hold, s)):
  %Equal.sym(Wr.Dec<List<&2, B.Hold>>, Wr.get_list(~B.Hold, ~FBg.get_hold, s), LawsBase.wire_read_list(~B.Hold, ~FBg.get_hold, s), Wire.wire_list_reads_items(~B.Hold, ~FBg.get_hold, s)) : bx.HLP(s, _)
  bx.hold_count(s, Wr.get_nat(s), {==})

# The account
# -----------

# what an account reader's answer says about its input s
def bx.CP(s: String, d: Wr.Dec<B.Acct>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Budget.sp_w_acct(x, r) : String} & {Budget.sp_fit_acct(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def bx.acct_5(-s: String, +fr: B.Amt, +sp: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +sk: String, pre: {s == Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, h, sk))))) : String}, f0_fr: {Budget.sp_fit_amt(fr) == True{} : Bool}, f0_sp: {Budget.sp_fit_amt(sp) == True{} : Bool}, f0_l: {Budget.sp_fit_amt(l) == True{} : Bool}, f0_o: {Budget.sp_fit_amt(o) == True{} : Bool}, f0_h: {LawsBase.wire_fits(List.length(&2, B.Hold, h)) == True{} : Bool}, f1_h: {Budget.sp_fit_holds(h) == True{} : Bool}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.CP(s, FBg.get_acct.until(fr, sp, l, o, h, d)):
  match d:
    case Wr.Got{+u, +sn}:
      (e, f0_u) = np
      (Equal.trans(String, s, Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, h, sk))))), Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, h, Wr.put_nat(u, sn)))))), pre, Equal.cong(String, String, z => Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, h, z))))), sk, Wr.put_nat(u, sn), e)), LBool.cb_and_intro(Budget.sp_fit_amt(fr), Bool.and(Budget.sp_fit_amt(sp), Bool.and(Budget.sp_fit_amt(l), Bool.and(Budget.sp_fit_amt(o), Bool.and(LawsBase.wire_fits(List.length(&2, B.Hold, h)), Bool.and(Budget.sp_fit_holds(h), LawsBase.wire_fits(u)))))), f0_fr, LBool.cb_and_intro(Budget.sp_fit_amt(sp), Bool.and(Budget.sp_fit_amt(l), Bool.and(Budget.sp_fit_amt(o), Bool.and(LawsBase.wire_fits(List.length(&2, B.Hold, h)), Bool.and(Budget.sp_fit_holds(h), LawsBase.wire_fits(u))))), f0_sp, LBool.cb_and_intro(Budget.sp_fit_amt(l), Bool.and(Budget.sp_fit_amt(o), Bool.and(LawsBase.wire_fits(List.length(&2, B.Hold, h)), Bool.and(Budget.sp_fit_holds(h), LawsBase.wire_fits(u)))), f0_l, LBool.cb_and_intro(Budget.sp_fit_amt(o), Bool.and(LawsBase.wire_fits(List.length(&2, B.Hold, h)), Bool.and(Budget.sp_fit_holds(h), LawsBase.wire_fits(u))), f0_o, LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, B.Hold, h)), Bool.and(Budget.sp_fit_holds(h), LawsBase.wire_fits(u)), f0_h, LBool.cb_and_intro(Budget.sp_fit_holds(h), LawsBase.wire_fits(u), f1_h, f0_u)))))))
    case Wr.Bad{}:
      Unit{}

def bx.acct_4(-s: String, +fr: B.Amt, +sp: B.Amt, +l: B.Amt, +o: B.Amt, +sk: String, pre: {s == Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, sk)))) : String}, f0_fr: {Budget.sp_fit_amt(fr) == True{} : Bool}, f0_sp: {Budget.sp_fit_amt(sp) == True{} : Bool}, f0_l: {Budget.sp_fit_amt(l) == True{} : Bool}, f0_o: {Budget.sp_fit_amt(o) == True{} : Bool}, d: Wr.Dec<List<&2, B.Hold>>, np: bx.HLP(sk, d)) -> bx.CP(s, FBg.get_acct.holds(fr, sp, l, o, d)):
  match d:
    case Wr.Got{+h, +sn}:
      (e, (f0_h, f1_h)) = np
      bx.acct_5(s, fr, sp, l, o, h, sn, Equal.trans(String, s, Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, sk)))), Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, h, sn))))), pre, Equal.cong(String, String, z => Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, z)))), sk, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, h, sn), e)), f0_fr, f0_sp, f0_l, f0_o, f0_h, f1_h, Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

def bx.acct_3(-s: String, +fr: B.Amt, +sp: B.Amt, +l: B.Amt, +sk: String, pre: {s == Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, sk))) : String}, f0_fr: {Budget.sp_fit_amt(fr) == True{} : Bool}, f0_sp: {Budget.sp_fit_amt(sp) == True{} : Bool}, f0_l: {Budget.sp_fit_amt(l) == True{} : Bool}, d: Wr.Dec<B.Amt>, np: bx.AP(sk, d)) -> bx.CP(s, FBg.get_acct.over(fr, sp, l, d)):
  match d:
    case Wr.Got{+o, +sn}:
      (e, f0_o) = np
      bx.acct_4(s, fr, sp, l, o, sn, Equal.trans(String, s, Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, sk))), Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, Budget.sp_w_amt(o, sn)))), pre, Equal.cong(String, String, z => Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, z))), sk, Budget.sp_w_amt(o, sn), e)), f0_fr, f0_sp, f0_l, f0_o, Wr.get_list(~B.Hold, ~FBg.get_hold, sn), bx.holds(sn))
    case Wr.Bad{}:
      Unit{}

def bx.acct_2(-s: String, +fr: B.Amt, +sp: B.Amt, +sk: String, pre: {s == Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, sk)) : String}, f0_fr: {Budget.sp_fit_amt(fr) == True{} : Bool}, f0_sp: {Budget.sp_fit_amt(sp) == True{} : Bool}, d: Wr.Dec<B.Amt>, np: bx.AP(sk, d)) -> bx.CP(s, FBg.get_acct.lent(fr, sp, d)):
  match d:
    case Wr.Got{+l, +sn}:
      (e, f0_l) = np
      bx.acct_3(s, fr, sp, l, sn, Equal.trans(String, s, Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, sk)), Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, Budget.sp_w_amt(l, sn))), pre, Equal.cong(String, String, z => Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, z)), sk, Budget.sp_w_amt(l, sn), e)), f0_fr, f0_sp, f0_l, FBg.get_amt(sn), bx.amt(sn))
    case Wr.Bad{}:
      Unit{}

def bx.acct_1(-s: String, +fr: B.Amt, +sk: String, pre: {s == Budget.sp_w_amt(fr, sk) : String}, f0_fr: {Budget.sp_fit_amt(fr) == True{} : Bool}, d: Wr.Dec<B.Amt>, np: bx.AP(sk, d)) -> bx.CP(s, FBg.get_acct.spent(fr, d)):
  match d:
    case Wr.Got{+sp, +sn}:
      (e, f0_sp) = np
      bx.acct_2(s, fr, sp, sn, Equal.trans(String, s, Budget.sp_w_amt(fr, sk), Budget.sp_w_amt(fr, Budget.sp_w_amt(sp, sn)), pre, Equal.cong(String, String, z => Budget.sp_w_amt(fr, z), sk, Budget.sp_w_amt(sp, sn), e)), f0_fr, f0_sp, FBg.get_amt(sn), bx.amt(sn))
    case Wr.Bad{}:
      Unit{}

def bx.acct_0(-s: String, +sk: String, pre: {s == sk : String}, d: Wr.Dec<B.Amt>, np: bx.AP(sk, d)) -> bx.CP(s, FBg.get_acct.free(d)):
  match d:
    case Wr.Got{+fr, +sn}:
      (e, f0_fr) = np
      bx.acct_1(s, fr, sn, Equal.trans(String, s, sk, Budget.sp_w_amt(fr, sn), pre, Equal.cong(String, String, z => z, sk, Budget.sp_w_amt(fr, sn), e)), f0_fr, FBg.get_amt(sn), bx.amt(sn))
    case Wr.Bad{}:
      Unit{}

# the account reader accepts only spelled accounts that fit
def bx.acct(+s: String) -> bx.CP(s, FBg.get_acct(s)):
  bx.acct_0(s, s, {==}, FBg.get_amt(s), bx.amt(s))

# The request
# -----------

# what the request reader's answer says about its input s
def bx.RP(s: String, d: Wr.Dec<FBg.Req>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Budget.sp_w_req(x, r) : String} & {Budget.sp_fit_req(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a reserve after its use, field by field (the last field first: a stage
# calls the next)
def bx.reserve_8(-s: String, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, sk)))))))))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, f0_base: {Budget.sp_fit_ask(base) == True{} : Bool}, f0_keep: {Budget.sp_fit_ask(keep) == True{} : Bool}, f0_step: {Budget.sp_fit_ask(step) == True{} : Bool}, f0_want: {Budget.sp_fit_ask(want) == True{} : Bool}, f0_less: {LawsBase.wire_fits(List.length(&2, B.Ask, less)) == True{} : Bool}, f1_less: {Budget.sp_fit_asks(less) == True{} : Bool}, d: Wr.Dec<B.Acct>, np: bx.CP(sk, d)) -> bx.RP(s, FBg.get_reserve.acct(u, p, id, now, base, keep, step, want, less, d)):
  match d:
    case Wr.Got{+a, +sn}:
      (e, f0_a) = np
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, sk)))))))))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, Budget.sp_w_acct(a, sn))))))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, z)))))))))), sk, Budget.sp_w_acct(a, sn), e)), LBool.cb_and_intro(LawsBase.wire_fits(id), Bool.and(LawsBase.wire_fits(now), Bool.and(Budget.sp_fit_ask(base), Bool.and(Budget.sp_fit_ask(keep), Bool.and(Budget.sp_fit_ask(step), Bool.and(Budget.sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a)))))))), f0_id, LBool.cb_and_intro(LawsBase.wire_fits(now), Bool.and(Budget.sp_fit_ask(base), Bool.and(Budget.sp_fit_ask(keep), Bool.and(Budget.sp_fit_ask(step), Bool.and(Budget.sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a))))))), f0_now, LBool.cb_and_intro(Budget.sp_fit_ask(base), Bool.and(Budget.sp_fit_ask(keep), Bool.and(Budget.sp_fit_ask(step), Bool.and(Budget.sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a)))))), f0_base, LBool.cb_and_intro(Budget.sp_fit_ask(keep), Bool.and(Budget.sp_fit_ask(step), Bool.and(Budget.sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a))))), f0_keep, LBool.cb_and_intro(Budget.sp_fit_ask(step), Bool.and(Budget.sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a)))), f0_step, LBool.cb_and_intro(Budget.sp_fit_ask(want), Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a))), f0_want, LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, B.Ask, less)), Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a)), f0_less, LBool.cb_and_intro(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a), f1_less, f0_a)))))))))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_7(-s: String, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, sk))))))))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, f0_base: {Budget.sp_fit_ask(base) == True{} : Bool}, f0_keep: {Budget.sp_fit_ask(keep) == True{} : Bool}, f0_step: {Budget.sp_fit_ask(step) == True{} : Bool}, f0_want: {Budget.sp_fit_ask(want) == True{} : Bool}, d: Wr.Dec<List<&2, B.Ask>>, np: bx.LP(sk, d)) -> bx.RP(s, FBg.get_reserve.less(u, p, id, now, base, keep, step, want, d)):
  match d:
    case Wr.Got{+less, +sn}:
      (e, (f0_less, f1_less)) = np
      bx.reserve_8(s, u, p, id, now, base, keep, step, want, less, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, sk))))))))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, sn)))))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, z))))))))), sk, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, sn), e)), f0_id, f0_now, f0_base, f0_keep, f0_step, f0_want, f0_less, f1_less, FBg.get_acct(sn), bx.acct(sn))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_6(-s: String, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, sk)))))))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, f0_base: {Budget.sp_fit_ask(base) == True{} : Bool}, f0_keep: {Budget.sp_fit_ask(keep) == True{} : Bool}, f0_step: {Budget.sp_fit_ask(step) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: bx.KP(sk, d)) -> bx.RP(s, FBg.get_reserve.want(u, p, id, now, base, keep, step, d)):
  match d:
    case Wr.Got{+want, +sn}:
      (e, f0_want) = np
      bx.reserve_7(s, u, p, id, now, base, keep, step, want, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, sk)))))))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, Budget.sp_w_ask(want, sn))))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, z)))))))), sk, Budget.sp_w_ask(want, sn), e)), f0_id, f0_now, f0_base, f0_keep, f0_step, f0_want, Wr.get_list(~B.Ask, ~FBg.get_ask, sn), bx.asks(sn))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_5(-s: String, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, sk))))))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, f0_base: {Budget.sp_fit_ask(base) == True{} : Bool}, f0_keep: {Budget.sp_fit_ask(keep) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: bx.KP(sk, d)) -> bx.RP(s, FBg.get_reserve.step(u, p, id, now, base, keep, d)):
  match d:
    case Wr.Got{+step, +sn}:
      (e, f0_step) = np
      bx.reserve_6(s, u, p, id, now, base, keep, step, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, sk))))))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, Budget.sp_w_ask(step, sn)))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, z))))))), sk, Budget.sp_w_ask(step, sn), e)), f0_id, f0_now, f0_base, f0_keep, f0_step, FBg.get_ask(sn), bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_4(-s: String, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, sk)))))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, f0_base: {Budget.sp_fit_ask(base) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: bx.KP(sk, d)) -> bx.RP(s, FBg.get_reserve.keep(u, p, id, now, base, d)):
  match d:
    case Wr.Got{+keep, +sn}:
      (e, f0_keep) = np
      bx.reserve_5(s, u, p, id, now, base, keep, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, sk)))))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, Budget.sp_w_ask(keep, sn))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, z)))))), sk, Budget.sp_w_ask(keep, sn), e)), f0_id, f0_now, f0_base, f0_keep, FBg.get_ask(sn), bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_3(-s: String, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, sk))))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: bx.KP(sk, d)) -> bx.RP(s, FBg.get_reserve.base(u, p, id, now, d)):
  match d:
    case Wr.Got{+base, +sn}:
      (e, f0_base) = np
      bx.reserve_4(s, u, p, id, now, base, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, sk))))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, Budget.sp_w_ask(base, sn)))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, z))))), sk, Budget.sp_w_ask(base, sn), e)), f0_id, f0_now, f0_base, FBg.get_ask(sn), bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_2(-s: String, +u: B.Use, +p: B.Phase, +id: Nat, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, sk)))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.RP(s, FBg.get_reserve.now(u, p, id, d)):
  match d:
    case Wr.Got{+now, +sn}:
      (e, f0_now) = np
      bx.reserve_3(s, u, p, id, now, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, sk)))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, Wr.put_nat(now, sn))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, z)))), sk, Wr.put_nat(now, sn), e)), f0_id, f0_now, FBg.get_ask(sn), bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_1(-s: String, +u: B.Use, +p: B.Phase, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), sk))) : String}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.RP(s, FBg.get_reserve.id(u, p, d)):
  match d:
    case Wr.Got{+id, +sn}:
      (e, f0_id) = np
      bx.reserve_2(s, u, p, id, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), sk))), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(id, sn)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), z))), sk, Wr.put_nat(id, sn), e)), f0_id, Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

def bx.reserve_0(-s: String, +u: B.Use, +sk: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), sk)) : String}, d: Wr.Dec<B.Phase>, np: bx.PP(sk, d)) -> bx.RP(s, FBg.get_reserve.phase(u, d)):
  match d:
    case Wr.Got{+p, +sn}:
      bx.reserve_1(s, u, p, sn, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), sk)), Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(Budget.sp_phase_tag(p), sn))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), z)), sk, Wr.put_nat(Budget.sp_phase_tag(p), sn), np)), Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

# a settle, field by field (the last field first: a stage calls the next)
def bx.settle_2(-s: String, +id: Nat, +act: B.Amt, +sk: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(id, Budget.sp_w_amt(act, sk))) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, f0_act: {Budget.sp_fit_amt(act) == True{} : Bool}, d: Wr.Dec<B.Acct>, np: bx.CP(sk, d)) -> bx.RP(s, FBg.get_settle.acct(id, act, d)):
  match d:
    case Wr.Got{+a, +sn}:
      (e, f0_a) = np
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(id, Budget.sp_w_amt(act, sk))), Wr.put_nat(1n, Wr.put_nat(id, Budget.sp_w_amt(act, Budget.sp_w_acct(a, sn)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(id, Budget.sp_w_amt(act, z))), sk, Budget.sp_w_acct(a, sn), e)), LBool.cb_and_intro(LawsBase.wire_fits(id), Bool.and(Budget.sp_fit_amt(act), Budget.sp_fit_acct(a)), f0_id, LBool.cb_and_intro(Budget.sp_fit_amt(act), Budget.sp_fit_acct(a), f0_act, f0_a)))
    case Wr.Bad{}:
      Unit{}

def bx.settle_1(-s: String, +id: Nat, +sk: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(id, sk)) : String}, f0_id: {LawsBase.wire_fits(id) == True{} : Bool}, d: Wr.Dec<B.Amt>, np: bx.AP(sk, d)) -> bx.RP(s, FBg.get_settle.act(id, d)):
  match d:
    case Wr.Got{+act, +sn}:
      (e, f0_act) = np
      bx.settle_2(s, id, act, sn, Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(id, sk)), Wr.put_nat(1n, Wr.put_nat(id, Budget.sp_w_amt(act, sn))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(id, z)), sk, Budget.sp_w_amt(act, sn), e)), f0_id, f0_act, FBg.get_acct(sn), bx.acct(sn))
    case Wr.Bad{}:
      Unit{}

def bx.settle_0(-s: String, +sk: String, pre: {s == Wr.put_nat(1n, sk) : String}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.RP(s, FBg.get_settle(d)):
  match d:
    case Wr.Got{+id, +sn}:
      (e, f0_id) = np
      bx.settle_1(s, id, sn, Equal.trans(String, s, Wr.put_nat(1n, sk), Wr.put_nat(1n, Wr.put_nat(id, sn)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), sk, Wr.put_nat(id, sn), e)), f0_id, FBg.get_amt(sn), bx.amt(sn))
    case Wr.Bad{}:
      Unit{}

# a carve, field by field (the last field first: a stage calls the next)
def bx.carve_4(-s: String, +p: B.Phase, +now: Nat, +want: B.Ask, +base: B.Ask, +sk: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, Budget.sp_w_ask(base, sk))))) : String}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, f0_want: {Budget.sp_fit_ask(want) == True{} : Bool}, f0_base: {Budget.sp_fit_ask(base) == True{} : Bool}, d: Wr.Dec<B.Acct>, np: bx.CP(sk, d)) -> bx.RP(s, FBg.get_carve.acct(p, now, want, base, d)):
  match d:
    case Wr.Got{+a, +sn}:
      (e, f0_a) = np
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, Budget.sp_w_ask(base, sk))))), Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, Budget.sp_w_ask(base, Budget.sp_w_acct(a, sn)))))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, Budget.sp_w_ask(base, z))))), sk, Budget.sp_w_acct(a, sn), e)), LBool.cb_and_intro(LawsBase.wire_fits(now), Bool.and(Budget.sp_fit_ask(want), Bool.and(Budget.sp_fit_ask(base), Budget.sp_fit_acct(a))), f0_now, LBool.cb_and_intro(Budget.sp_fit_ask(want), Bool.and(Budget.sp_fit_ask(base), Budget.sp_fit_acct(a)), f0_want, LBool.cb_and_intro(Budget.sp_fit_ask(base), Budget.sp_fit_acct(a), f0_base, f0_a))))
    case Wr.Bad{}:
      Unit{}

def bx.carve_3(-s: String, +p: B.Phase, +now: Nat, +want: B.Ask, +sk: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, sk)))) : String}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, f0_want: {Budget.sp_fit_ask(want) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: bx.KP(sk, d)) -> bx.RP(s, FBg.get_carve.base(p, now, want, d)):
  match d:
    case Wr.Got{+base, +sn}:
      (e, f0_base) = np
      bx.carve_4(s, p, now, want, base, sn, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, sk)))), Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, Budget.sp_w_ask(base, sn))))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, z)))), sk, Budget.sp_w_ask(base, sn), e)), f0_now, f0_want, f0_base, FBg.get_acct(sn), bx.acct(sn))
    case Wr.Bad{}:
      Unit{}

def bx.carve_2(-s: String, +p: B.Phase, +now: Nat, +sk: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, sk))) : String}, f0_now: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<B.Ask>, np: bx.KP(sk, d)) -> bx.RP(s, FBg.get_carve.want(p, now, d)):
  match d:
    case Wr.Got{+want, +sn}:
      (e, f0_want) = np
      bx.carve_3(s, p, now, want, sn, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, sk))), Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, Budget.sp_w_ask(want, sn)))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, z))), sk, Budget.sp_w_ask(want, sn), e)), f0_now, f0_want, FBg.get_ask(sn), bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

def bx.carve_1(-s: String, +p: B.Phase, +sk: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), sk)) : String}, d: Wr.Dec<Nat>, np: bx.NP(sk, d)) -> bx.RP(s, FBg.get_carve.now(p, d)):
  match d:
    case Wr.Got{+now, +sn}:
      (e, f0_now) = np
      bx.carve_2(s, p, now, sn, Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), sk)), Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), Wr.put_nat(now, sn))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), z)), sk, Wr.put_nat(now, sn), e)), f0_now, FBg.get_ask(sn), bx.ask(sn))
    case Wr.Bad{}:
      Unit{}

def bx.carve_0(-s: String, +sk: String, pre: {s == Wr.put_nat(2n, sk) : String}, d: Wr.Dec<B.Phase>, np: bx.PP(sk, d)) -> bx.RP(s, FBg.get_carve(d)):
  match d:
    case Wr.Got{+p, +sn}:
      bx.carve_1(s, p, sn, Equal.trans(String, s, Wr.put_nat(2n, sk), Wr.put_nat(2n, Wr.put_nat(Budget.sp_phase_tag(p), sn)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), sk, Wr.put_nat(Budget.sp_phase_tag(p), sn), np)), Wr.get_nat(sn), bx.nat(sn))
    case Wr.Bad{}:
      Unit{}

# a close, field by field (the last field first: a stage calls the next)
def bx.close_1(-s: String, +c: B.Acct, +sk: String, pre: {s == Wr.put_nat(3n, Budget.sp_w_acct(c, sk)) : String}, f0_c: {Budget.sp_fit_acct(c) == True{} : Bool}, d: Wr.Dec<B.Acct>, np: bx.CP(sk, d)) -> bx.RP(s, FBg.get_close.parent(c, d)):
  match d:
    case Wr.Got{+p, +sn}:
      (e, f0_p) = np
      (Equal.trans(String, s, Wr.put_nat(3n, Budget.sp_w_acct(c, sk)), Wr.put_nat(3n, Budget.sp_w_acct(c, Budget.sp_w_acct(p, sn))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, Budget.sp_w_acct(c, z)), sk, Budget.sp_w_acct(p, sn), e)), LBool.cb_and_intro(Budget.sp_fit_acct(c), Budget.sp_fit_acct(p), f0_c, f0_p))
    case Wr.Bad{}:
      Unit{}

def bx.close_0(-s: String, +sk: String, pre: {s == Wr.put_nat(3n, sk) : String}, d: Wr.Dec<B.Acct>, np: bx.CP(sk, d)) -> bx.RP(s, FBg.get_close(d)):
  match d:
    case Wr.Got{+c, +sn}:
      (e, f0_c) = np
      bx.close_1(s, c, sn, Equal.trans(String, s, Wr.put_nat(3n, sk), Wr.put_nat(3n, Budget.sp_w_acct(c, sn)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), sk, Budget.sp_w_acct(c, sn), e)), f0_c, FBg.get_acct(sn), bx.acct(sn))
    case Wr.Bad{}:
      Unit{}

# a fund, field by field (the last field first: a stage calls the next)
def bx.fund_1(-s: String, +n: B.Ask, +sk: String, pre: {s == Wr.put_nat(4n, Budget.sp_w_ask(n, sk)) : String}, f0_n: {Budget.sp_fit_ask(n) == True{} : Bool}, d: Wr.Dec<B.Acct>, np: bx.CP(sk, d)) -> bx.RP(s, FBg.get_fund.acct(n, d)):
  match d:
    case Wr.Got{+a, +sn}:
      (e, f0_a) = np
      (Equal.trans(String, s, Wr.put_nat(4n, Budget.sp_w_ask(n, sk)), Wr.put_nat(4n, Budget.sp_w_ask(n, Budget.sp_w_acct(a, sn))), pre, Equal.cong(String, String, z => Wr.put_nat(4n, Budget.sp_w_ask(n, z)), sk, Budget.sp_w_acct(a, sn), e)), LBool.cb_and_intro(Budget.sp_fit_ask(n), Budget.sp_fit_acct(a), f0_n, f0_a))
    case Wr.Bad{}:
      Unit{}

def bx.fund_0(-s: String, +sk: String, pre: {s == Wr.put_nat(4n, sk) : String}, d: Wr.Dec<B.Ask>, np: bx.KP(sk, d)) -> bx.RP(s, FBg.get_fund(d)):
  match d:
    case Wr.Got{+n, +sn}:
      (e, f0_n) = np
      bx.fund_1(s, n, sn, Equal.trans(String, s, Wr.put_nat(4n, sk), Wr.put_nat(4n, Budget.sp_w_ask(n, sn)), pre, Equal.cong(String, String, z => Wr.put_nat(4n, z), sk, Budget.sp_w_ask(n, sn), e)), f0_n, FBg.get_acct(sn), bx.acct(sn))
    case Wr.Bad{}:
      Unit{}

# the use of tag t, then the rest of a reserve
def bx.use(t: Nat, -s: String, +s2: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(t, s2)) : String}) -> bx.RP(s, FBg.get_reserve.use(t, s2)):
  match t:
    case 0n:
      bx.reserve_0(s, B.Work{}, s2, pre, FBg.get_phase(s2), bx.phase(s2))
    case 1n+a:
      match a:
        case 0n:
          bx.reserve_0(s, B.Final{}, s2, pre, FBg.get_phase(s2), bx.phase(s2))
        case 1n+b:
          match b:
            case 0n:
              bx.reserve_0(s, B.Side{}, s2, pre, FBg.get_phase(s2), bx.phase(s2))
            case 1n+c:
              Unit{}

def bx.reserve(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, np: bx.NP(s1, d)) -> bx.RP(s, FBg.get_reserve(d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e, f) = np
      bx.use(t, s, s2, Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_nat(t, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_nat(t, s2), e)))
    case Wr.Bad{}:
      Unit{}

# the request of tag n
def bx.of(n: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> bx.RP(s, FBg.get_req.of(n, s1)):
  match n:
    case 0n:
      bx.reserve(s, s1, pre, Wr.get_nat(s1), bx.nat(s1))
    case 1n+a:
      match a:
        case 0n:
          bx.settle_0(s, s1, pre, Wr.get_nat(s1), bx.nat(s1))
        case 1n+b:
          match b:
            case 0n:
              bx.carve_0(s, s1, pre, FBg.get_phase(s1), bx.phase(s1))
            case 1n+c:
              match c:
                case 0n:
                  bx.close_0(s, s1, pre, FBg.get_acct(s1), bx.acct(s1))
                case 1n+g:
                  match g:
                    case 0n:
                      bx.fund_0(s, s1, pre, FBg.get_ask(s1), bx.ask(s1))
                    case 1n+h:
                      Unit{}

def bx.tag(-s: String, d: Wr.Dec<Nat>, np: bx.NP(s, d)) -> bx.RP(s, FBg.get_req.tag(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = np
      bx.of(n, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the request reader accepts only spelled requests that fit
def bx.req(+s: String) -> bx.RP(s, FBg.get_req(s)):
  bx.tag(s, Wr.get_nat(s), bx.nat(s))
