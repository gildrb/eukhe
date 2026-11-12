# eukhe: lemmas of the entry proofs of area budget (bend/ffi_budget.bend):
# a spelled request that fits reads back (be.req_rt: each decoder reads its
# spelling field by field with wire_nat_round_trip, a list by the generic
# list laws wire_list_spells_items and wire_list_reads_items, with
# put_nat == wire_dec by LAWireDec.wdec.nat), the answer is the model's decision spelled
# (be.reply: each encoder is the spec's spelling), no answer opens with 'E'
# (be.answer_ok), and an answer that opens with 'E' is the one error form
# (be.refuse)

import Base
import ../../../bend/budget.bend as B
import ../../../bend/ffi_budget.bend as FBg
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/budget.bend as Budget
import ../../base/wire.bend as LWire
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../wire/base/dec.bend as LAWireDec
import ../../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../../wire/wire_list_spells_items.bend as PWireListSpellsItems

# Bool
# ----

def be.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def be.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : be.If(_, G)
  Unit{}

def be.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def be.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      be.absurd({b == True{} : Bool}, e)

# Round trip: the fields
# ----------------------
# Each lemma is stated as the rewrite it is used for: the answer Got{x,
# rest} on the left, the decoder on the spelling on the right.

# a spelled Nat that fits reads back
def be.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# a spelled amount that fits reads back
def be.amt(x: B.Amt, +rest: String, h: {Budget.sp_fit_amt(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FBg.get_amt(Budget.sp_w_amt(x, rest)) : Wr.Dec<B.Amt>}:
  match x:
    case B.Amt{+c, +k, +n, +r}:
      +h0 = h
      +fc = be.and_l(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(r))), h0)
      +h1 = be.and_r(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(r))), h0)
      +fk = be.and_l(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(r)), h1)
      +h2 = be.and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(r)), h1)
      +fn = be.and_l(LawsBase.wire_fits(n), LawsBase.wire_fits(r), h2)
      +fr = be.and_r(LawsBase.wire_fits(n), LawsBase.wire_fits(r), h2)
      +v = {Wr.Got{B.Amt{c, k, n, r}, rest} : Wr.Dec<B.Amt>}
      %be.nat(c, Wr.put_nat(k, Wr.put_nat(n, Wr.put_nat(r, rest))), fc) : {v == FBg.get_amt.c(_) : Wr.Dec<B.Amt>}
      %be.nat(k, Wr.put_nat(n, Wr.put_nat(r, rest)), fk) : {v == FBg.get_amt.k(c, _) : Wr.Dec<B.Amt>}
      %be.nat(n, Wr.put_nat(r, rest), fn) : {v == FBg.get_amt.n(c, k, _) : Wr.Dec<B.Amt>}
      %be.nat(r, rest, fr) : {v == FBg.get_amt.r(c, k, n, _) : Wr.Dec<B.Amt>}
      {==}

# a spelled ask that fits reads back
def be.ask(x: B.Ask, +rest: String, h: {Budget.sp_fit_ask(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FBg.get_ask(Budget.sp_w_ask(x, rest)) : Wr.Dec<B.Ask>}:
  match x:
    case B.Ask{+a, +m}:
      +h0 = h
      +fa = be.and_l(Budget.sp_fit_amt(a), LawsBase.wire_fits(m), h0)
      +fm = be.and_r(Budget.sp_fit_amt(a), LawsBase.wire_fits(m), h0)
      +v = {Wr.Got{B.Ask{a, m}, rest} : Wr.Dec<B.Ask>}
      %be.amt(a, Wr.put_nat(m, rest), fa) : {v == FBg.get_ask.amt(_) : Wr.Dec<B.Ask>}
      %be.nat(m, rest, fm) : {v == FBg.get_ask.ms(a, _) : Wr.Dec<B.Ask>}
      {==}

# a spelled hold that fits reads back
def be.hold(+i: Nat, +x: B.Amt, +rest: String, fi: {LawsBase.wire_fits(i) == True{} : Bool}, fx: {Budget.sp_fit_amt(x) == True{} : Bool}) -> {Wr.Got{B.Hold{i, x}, rest} == FBg.get_hold(Budget.sp_w_hold(B.Hold{i, x}, rest)) : Wr.Dec<B.Hold>}:
  %be.nat(i, Budget.sp_w_amt(x, rest), fi) : {Wr.Got{B.Hold{i, x}, rest} == FBg.get_hold.id(_) : Wr.Dec<B.Hold>}
  %be.amt(x, rest, fx) : {Wr.Got{B.Hold{i, x}, rest} == FBg.get_hold.amt(i, _) : Wr.Dec<B.Hold>}
  {==}

# a spelled phase reads back
def be.phase(p: B.Phase, rest: String) -> {Wr.Got{p, rest} == FBg.get_phase(Wr.put_nat(Budget.sp_phase_tag(p), rest)) : Wr.Dec<B.Phase>}:
  match p:
    case B.Working{}:
      {==}
    case B.WrapUp{}:
      {==}
    case B.Exhausted{}:
      {==}

# Round trip: the lists
# ---------------------

# the spec's item loop reads the spelled asks back
def be.ask_items(xs: List<&2, B.Ask>, +rest: String, h: {Budget.sp_fit_asks(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == LawsBase.wire_items(~B.Ask, ~FBg.get_ask, List.length(&2, B.Ask, xs), LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, rest)) : Wr.Dec<List<&2, B.Ask>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = h
      +fx = be.and_l(Budget.sp_fit_ask(x), Budget.sp_fit_asks(t), h0)
      +ft = be.and_r(Budget.sp_fit_ask(x), Budget.sp_fit_asks(t), h0)
      +m = List.length(&2, B.Ask, t)
      +s1 = LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, t, rest)
      %be.ask(x, s1, fx) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.then(B.Ask, _, r => LawsBase.wire_items(~B.Ask, ~FBg.get_ask, m, r)) : Wr.Dec<List<&2, B.Ask>>}
      %be.ask_items(t, rest, ft) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.cons(B.Ask, x, _) : Wr.Dec<List<&2, B.Ask>>}
      {==}

# a spelled list of asks that fits reads back
def be.asks(+xs: List<&2, B.Ask>, +rest: String, fc: {LawsBase.wire_fits(List.length(&2, B.Ask, xs)) == True{} : Bool}, fx: {Budget.sp_fit_asks(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~B.Ask, ~FBg.get_ask, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, xs, rest)) : Wr.Dec<List<&2, B.Ask>>}:
  +n = List.length(&2, B.Ask, xs)
  +s1 = LawsBase.wire_put_items(~B.Ask, ~Budget.sp_w_ask, xs, rest)
  %Equal.sym(String, Wr.put_list(~B.Ask, ~Budget.sp_w_ask, xs, rest), LawsBase.wire_dec(n, s1), Wire.wire_list_spells_items(~B.Ask, ~Budget.sp_w_ask, xs, rest)) : {Wr.Got{xs, rest} == Wr.get_list(~B.Ask, ~FBg.get_ask, _) : Wr.Dec<List<&2, B.Ask>>}
  %LAWireDec.wdec.nat(n, s1) : {Wr.Got{xs, rest} == Wr.get_list(~B.Ask, ~FBg.get_ask, _) : Wr.Dec<List<&2, B.Ask>>}
  %Equal.sym(Wr.Dec<List<&2, B.Ask>>, Wr.get_list(~B.Ask, ~FBg.get_ask, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~B.Ask, ~FBg.get_ask, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~B.Ask, ~FBg.get_ask, Wr.put_nat(n, s1))) : {Wr.Got{xs, rest} == _ : Wr.Dec<List<&2, B.Ask>>}
  %be.nat(n, s1, fc) : {Wr.Got{xs, rest} == LawsBase.wire_read_list.count(~B.Ask, ~FBg.get_ask, _) : Wr.Dec<List<&2, B.Ask>>}
  be.ask_items(xs, rest, fx)

# the spec's item loop reads the spelled holds back
def be.hold_items(hs: List<&2, B.Hold>, +rest: String, h: {Budget.sp_fit_holds(hs) == True{} : Bool}) -> {Wr.Got{hs, rest} == LawsBase.wire_items(~B.Hold, ~FBg.get_hold, List.length(&2, B.Hold, hs), LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, hs, rest)) : Wr.Dec<List<&2, B.Hold>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{hd, +t}:
      match hd:
        case B.Hold{+i, +x}:
          +h0 = h
          +fi = be.and_l(LawsBase.wire_fits(i), Bool.and(Budget.sp_fit_amt(x), Budget.sp_fit_holds(t)), h0)
          +h1 = be.and_r(LawsBase.wire_fits(i), Bool.and(Budget.sp_fit_amt(x), Budget.sp_fit_holds(t)), h0)
          +fx = be.and_l(Budget.sp_fit_amt(x), Budget.sp_fit_holds(t), h1)
          +ft = be.and_r(Budget.sp_fit_amt(x), Budget.sp_fit_holds(t), h1)
          +m = List.length(&2, B.Hold, t)
          +s1 = LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, t, rest)
          %be.hold(i, x, s1, fi, fx) : {Wr.Got{B.Hold{i, x} <> t, rest} == LawsBase.wire_items.then(B.Hold, _, r => LawsBase.wire_items(~B.Hold, ~FBg.get_hold, m, r)) : Wr.Dec<List<&2, B.Hold>>}
          %be.hold_items(t, rest, ft) : {Wr.Got{B.Hold{i, x} <> t, rest} == LawsBase.wire_items.cons(B.Hold, B.Hold{i, x}, _) : Wr.Dec<List<&2, B.Hold>>}
          {==}

# a spelled list of holds that fits reads back
def be.holds(+hs: List<&2, B.Hold>, +rest: String, fc: {LawsBase.wire_fits(List.length(&2, B.Hold, hs)) == True{} : Bool}, fh: {Budget.sp_fit_holds(hs) == True{} : Bool}) -> {Wr.Got{hs, rest} == Wr.get_list(~B.Hold, ~FBg.get_hold, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, rest)) : Wr.Dec<List<&2, B.Hold>>}:
  +n = List.length(&2, B.Hold, hs)
  +s1 = LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, hs, rest)
  %Equal.sym(String, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, rest), LawsBase.wire_dec(n, s1), Wire.wire_list_spells_items(~B.Hold, ~Budget.sp_w_hold, hs, rest)) : {Wr.Got{hs, rest} == Wr.get_list(~B.Hold, ~FBg.get_hold, _) : Wr.Dec<List<&2, B.Hold>>}
  %LAWireDec.wdec.nat(n, s1) : {Wr.Got{hs, rest} == Wr.get_list(~B.Hold, ~FBg.get_hold, _) : Wr.Dec<List<&2, B.Hold>>}
  %Equal.sym(Wr.Dec<List<&2, B.Hold>>, Wr.get_list(~B.Hold, ~FBg.get_hold, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~B.Hold, ~FBg.get_hold, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~B.Hold, ~FBg.get_hold, Wr.put_nat(n, s1))) : {Wr.Got{hs, rest} == _ : Wr.Dec<List<&2, B.Hold>>}
  %be.nat(n, s1, fc) : {Wr.Got{hs, rest} == LawsBase.wire_read_list.count(~B.Hold, ~FBg.get_hold, _) : Wr.Dec<List<&2, B.Hold>>}
  be.hold_items(hs, rest, fh)

# Round trip: the account and the request
# ---------------------------------------

# a spelled account that fits reads back
def be.acct(a: B.Acct, +rest: String, h: {Budget.sp_fit_acct(a) == True{} : Bool}) -> {Wr.Got{a, rest} == FBg.get_acct(Budget.sp_w_acct(a, rest)) : Wr.Dec<B.Acct>}:
  match a:
    case B.Acct{+f, +s, +l, +o, +hs, +u}:
      +h0 = h
      +b6 = Bool.and(Budget.sp_fit_holds(hs), LawsBase.wire_fits(u))
      +b5 = Bool.and(LawsBase.wire_fits(List.length(&2, B.Hold, hs)), b6)
      +b4 = Bool.and(Budget.sp_fit_amt(o), b5)
      +b3 = Bool.and(Budget.sp_fit_amt(l), b4)
      +b2 = Bool.and(Budget.sp_fit_amt(s), b3)
      +ff = be.and_l(Budget.sp_fit_amt(f), b2, h0)
      +h1 = be.and_r(Budget.sp_fit_amt(f), b2, h0)
      +fs = be.and_l(Budget.sp_fit_amt(s), b3, h1)
      +h2 = be.and_r(Budget.sp_fit_amt(s), b3, h1)
      +fl = be.and_l(Budget.sp_fit_amt(l), b4, h2)
      +h3 = be.and_r(Budget.sp_fit_amt(l), b4, h2)
      +fo = be.and_l(Budget.sp_fit_amt(o), b5, h3)
      +h4 = be.and_r(Budget.sp_fit_amt(o), b5, h3)
      +fc = be.and_l(LawsBase.wire_fits(List.length(&2, B.Hold, hs)), b6, h4)
      +h5 = be.and_r(LawsBase.wire_fits(List.length(&2, B.Hold, hs)), b6, h4)
      +fh = be.and_l(Budget.sp_fit_holds(hs), LawsBase.wire_fits(u), h5)
      +fu = be.and_r(Budget.sp_fit_holds(hs), LawsBase.wire_fits(u), h5)
      +s6 = Wr.put_nat(u, rest)
      +s5 = Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, s6)
      +s4 = Budget.sp_w_amt(o, s5)
      +s3 = Budget.sp_w_amt(l, s4)
      +s2 = Budget.sp_w_amt(s, s3)
      +v = {Wr.Got{B.Acct{f, s, l, o, hs, u}, rest} : Wr.Dec<B.Acct>}
      %be.amt(f, s2, ff) : {v == FBg.get_acct.free(_) : Wr.Dec<B.Acct>}
      %be.amt(s, s3, fs) : {v == FBg.get_acct.spent(f, _) : Wr.Dec<B.Acct>}
      %be.amt(l, s4, fl) : {v == FBg.get_acct.lent(f, s, _) : Wr.Dec<B.Acct>}
      %be.amt(o, s5, fo) : {v == FBg.get_acct.over(f, s, l, _) : Wr.Dec<B.Acct>}
      %be.holds(hs, s6, fc, fh) : {v == FBg.get_acct.holds(f, s, l, o, _) : Wr.Dec<B.Acct>}
      %be.nat(u, rest, fu) : {v == FBg.get_acct.until(f, s, l, o, hs, _) : Wr.Dec<B.Acct>}
      {==}

# the spelled tag of a use reads back
def be.use_nat(u: B.Use, rest: String) -> {Wr.Got{Budget.sp_use_tag(u), rest} == Wr.get_nat(Wr.put_nat(Budget.sp_use_tag(u), rest)) : Wr.Dec<Nat>}:
  match u:
    case B.Work{}:
      {==}
    case B.Final{}:
      {==}
    case B.Side{}:
      {==}

# the tag of a use is read as that use
def be.use_of(u: B.Use, rest: String) -> {FBg.get_reserve.phase(u, FBg.get_phase(rest)) == FBg.get_reserve.use(Budget.sp_use_tag(u), rest) : Wr.Dec<FBg.Req>}:
  match u:
    case B.Work{}:
      {==}
    case B.Final{}:
      {==}
    case B.Side{}:
      {==}

# a spelled request that fits reads back, the rest untouched
def be.req_rt(q: FBg.Req, +rest: String, h: {Budget.sp_fit_req(q) == True{} : Bool}) -> {FBg.get_req(Budget.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FBg.Req>}:
  match q:
    case FBg.QReserve{+u, +p, +id, +now, +base, +keep, +want, +less, +a}:
      +h0 = h
      +b7 = Bool.and(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a))
      +b6 = Bool.and(LawsBase.wire_fits(List.length(&2, B.Ask, less)), b7)
      +b5 = Bool.and(Budget.sp_fit_ask(want), b6)
      +b4 = Bool.and(Budget.sp_fit_ask(keep), b5)
      +b3 = Bool.and(Budget.sp_fit_ask(base), b4)
      +b2 = Bool.and(LawsBase.wire_fits(now), b3)
      +fi = be.and_l(LawsBase.wire_fits(id), b2, h0)
      +h1 = be.and_r(LawsBase.wire_fits(id), b2, h0)
      +fn = be.and_l(LawsBase.wire_fits(now), b3, h1)
      +h2 = be.and_r(LawsBase.wire_fits(now), b3, h1)
      +fb = be.and_l(Budget.sp_fit_ask(base), b4, h2)
      +h3 = be.and_r(Budget.sp_fit_ask(base), b4, h2)
      +fk = be.and_l(Budget.sp_fit_ask(keep), b5, h3)
      +h4 = be.and_r(Budget.sp_fit_ask(keep), b5, h3)
      +fw = be.and_l(Budget.sp_fit_ask(want), b6, h4)
      +h5 = be.and_r(Budget.sp_fit_ask(want), b6, h4)
      +fc = be.and_l(LawsBase.wire_fits(List.length(&2, B.Ask, less)), b7, h5)
      +h6 = be.and_r(LawsBase.wire_fits(List.length(&2, B.Ask, less)), b7, h5)
      +fl = be.and_l(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a), h6)
      +fa = be.and_r(Budget.sp_fit_asks(less), Budget.sp_fit_acct(a), h6)
      +s9 = Budget.sp_w_acct(a, rest)
      +s8 = Wr.put_list(~B.Ask, ~Budget.sp_w_ask, less, s9)
      +s7 = Budget.sp_w_ask(want, s8)
      +s6 = Budget.sp_w_ask(keep, s7)
      +s5 = Budget.sp_w_ask(base, s6)
      +s4 = Wr.put_nat(now, s5)
      +s3 = Wr.put_nat(id, s4)
      +s2 = Wr.put_nat(Budget.sp_phase_tag(p), s3)
      +v = {Wr.Got{FBg.QReserve{u, p, id, now, base, keep, want, less, a}, rest} : Wr.Dec<FBg.Req>}
      %be.use_nat(u, s2) : {FBg.get_reserve(_) == v : Wr.Dec<FBg.Req>}
      %be.use_of(u, s2) : {_ == v : Wr.Dec<FBg.Req>}
      %be.phase(p, s3) : {FBg.get_reserve.phase(u, _) == v : Wr.Dec<FBg.Req>}
      %be.nat(id, s4, fi) : {FBg.get_reserve.id(u, p, _) == v : Wr.Dec<FBg.Req>}
      %be.nat(now, s5, fn) : {FBg.get_reserve.now(u, p, id, _) == v : Wr.Dec<FBg.Req>}
      %be.ask(base, s6, fb) : {FBg.get_reserve.base(u, p, id, now, _) == v : Wr.Dec<FBg.Req>}
      %be.ask(keep, s7, fk) : {FBg.get_reserve.keep(u, p, id, now, base, _) == v : Wr.Dec<FBg.Req>}
      %be.ask(want, s8, fw) : {FBg.get_reserve.want(u, p, id, now, base, keep, _) == v : Wr.Dec<FBg.Req>}
      %be.asks(less, s9, fc, fl) : {FBg.get_reserve.less(u, p, id, now, base, keep, want, _) == v : Wr.Dec<FBg.Req>}
      %be.acct(a, rest, fa) : {FBg.get_reserve.acct(u, p, id, now, base, keep, want, less, _) == v : Wr.Dec<FBg.Req>}
      {==}
    case FBg.QSettle{+id, +act, +a}:
      +h0 = h
      +fi = be.and_l(LawsBase.wire_fits(id), Bool.and(Budget.sp_fit_amt(act), Budget.sp_fit_acct(a)), h0)
      +h1 = be.and_r(LawsBase.wire_fits(id), Bool.and(Budget.sp_fit_amt(act), Budget.sp_fit_acct(a)), h0)
      +fx = be.and_l(Budget.sp_fit_amt(act), Budget.sp_fit_acct(a), h1)
      +fa = be.and_r(Budget.sp_fit_amt(act), Budget.sp_fit_acct(a), h1)
      +s3 = Budget.sp_w_acct(a, rest)
      +s2 = Budget.sp_w_amt(act, s3)
      +v = {Wr.Got{FBg.QSettle{id, act, a}, rest} : Wr.Dec<FBg.Req>}
      %be.nat(id, s2, fi) : {FBg.get_settle(_) == v : Wr.Dec<FBg.Req>}
      %be.amt(act, s3, fx) : {FBg.get_settle.act(id, _) == v : Wr.Dec<FBg.Req>}
      %be.acct(a, rest, fa) : {FBg.get_settle.acct(id, act, _) == v : Wr.Dec<FBg.Req>}
      {==}
    case FBg.QCarve{+p, +now, +want, +base, +a}:
      +h0 = h
      +b3 = Bool.and(Budget.sp_fit_ask(base), Budget.sp_fit_acct(a))
      +b2 = Bool.and(Budget.sp_fit_ask(want), b3)
      +fn = be.and_l(LawsBase.wire_fits(now), b2, h0)
      +h1 = be.and_r(LawsBase.wire_fits(now), b2, h0)
      +fw = be.and_l(Budget.sp_fit_ask(want), b3, h1)
      +h2 = be.and_r(Budget.sp_fit_ask(want), b3, h1)
      +fb = be.and_l(Budget.sp_fit_ask(base), Budget.sp_fit_acct(a), h2)
      +fa = be.and_r(Budget.sp_fit_ask(base), Budget.sp_fit_acct(a), h2)
      +s5 = Budget.sp_w_acct(a, rest)
      +s4 = Budget.sp_w_ask(base, s5)
      +s3 = Budget.sp_w_ask(want, s4)
      +s2 = Wr.put_nat(now, s3)
      +v = {Wr.Got{FBg.QCarve{p, now, want, base, a}, rest} : Wr.Dec<FBg.Req>}
      %be.phase(p, s2) : {FBg.get_carve(_) == v : Wr.Dec<FBg.Req>}
      %be.nat(now, s3, fn) : {FBg.get_carve.now(p, _) == v : Wr.Dec<FBg.Req>}
      %be.ask(want, s4, fw) : {FBg.get_carve.want(p, now, _) == v : Wr.Dec<FBg.Req>}
      %be.ask(base, s5, fb) : {FBg.get_carve.base(p, now, want, _) == v : Wr.Dec<FBg.Req>}
      %be.acct(a, rest, fa) : {FBg.get_carve.acct(p, now, want, base, _) == v : Wr.Dec<FBg.Req>}
      {==}
    case FBg.QClose{+c, +p}:
      +h0 = h
      +fc = be.and_l(Budget.sp_fit_acct(c), Budget.sp_fit_acct(p), h0)
      +fp = be.and_r(Budget.sp_fit_acct(c), Budget.sp_fit_acct(p), h0)
      +v = {Wr.Got{FBg.QClose{c, p}, rest} : Wr.Dec<FBg.Req>}
      %be.acct(c, Budget.sp_w_acct(p, rest), fc) : {FBg.get_close(_) == v : Wr.Dec<FBg.Req>}
      %be.acct(p, rest, fp) : {FBg.get_close.parent(c, _) == v : Wr.Dec<FBg.Req>}
      {==}
    case FBg.QFund{+n, +a}:
      +h0 = h
      +fx = be.and_l(Budget.sp_fit_ask(n), Budget.sp_fit_acct(a), h0)
      +fa = be.and_r(Budget.sp_fit_ask(n), Budget.sp_fit_acct(a), h0)
      +v = {Wr.Got{FBg.QFund{n, a}, rest} : Wr.Dec<FBg.Req>}
      %be.ask(n, Budget.sp_w_acct(a, rest), fx) : {FBg.get_fund(_) == v : Wr.Dec<FBg.Req>}
      %be.acct(a, rest, fa) : {FBg.get_fund.acct(n, _) == v : Wr.Dec<FBg.Req>}
      {==}

# Replies: the encoders are the spec's spellings
# ----------------------------------------------
# Each lemma takes the two rests and their equation, so the lemmas nest
# as the encoders do.

def be.w_amt(x: B.Amt, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FBg.put_amt(x, r1) == Budget.sp_w_amt(x, r2) : String}:
  match x:
    case B.Amt{c, k, n, r}:
      Equal.cong(String, String, z => Wr.put_nat(c, Wr.put_nat(k, Wr.put_nat(n, Wr.put_nat(r, z)))), r1, r2, e)

def be.w_ask(x: B.Ask, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FBg.put_ask(x, r1) == Budget.sp_w_ask(x, r2) : String}:
  match x:
    case B.Ask{a, +m}:
      be.w_amt(a, Wr.put_nat(m, r1), Wr.put_nat(m, r2), Equal.cong(String, String, z => Wr.put_nat(m, z), r1, r2, e))

def be.w_hold(hd: B.Hold, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FBg.put_hold(hd, r1) == Budget.sp_w_hold(hd, r2) : String}:
  match hd:
    case B.Hold{i, x}:
      Equal.cong(String, String, z => Wr.put_nat(i, z), FBg.put_amt(x, r1), Budget.sp_w_amt(x, r2), be.w_amt(x, r1, r2, e))

def be.w_phase(p: B.Phase, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FBg.put_phase(p, r1) == Wr.put_nat(Budget.sp_phase_tag(p), r2) : String}:
  match p:
    case B.Working{}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), r1, r2, e)
    case B.WrapUp{}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), r1, r2, e)
    case B.Exhausted{}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), r1, r2, e)

# the items of a list of holds, by either writer
def be.w_hold_items(hs: List<&2, B.Hold>, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {LawsBase.wire_put_items(~B.Hold, ~FBg.put_hold, hs, r1) == LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, hs, r2) : String}:
  match hs:
    case Nil{}:
      e
    case Con{hd, t}:
      be.w_hold(hd, LawsBase.wire_put_items(~B.Hold, ~FBg.put_hold, t, r1), LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, t, r2), be.w_hold_items(t, r1, r2, e))

# a list of holds, by either writer: the count, then the items
def be.w_holds(+hs: List<&2, B.Hold>, +r1: String, +r2: String, e: {r1 == r2 : String}) -> {Wr.put_list(~B.Hold, ~FBg.put_hold, hs, r1) == Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, r2) : String}:
  -n = List.length(&2, B.Hold, hs)
  -i1 = LawsBase.wire_put_items(~B.Hold, ~FBg.put_hold, hs, r1)
  -i2 = LawsBase.wire_put_items(~B.Hold, ~Budget.sp_w_hold, hs, r2)
  Equal.trans(String, Wr.put_list(~B.Hold, ~FBg.put_hold, hs, r1), LawsBase.wire_dec(n, i1), Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, r2),
    Wire.wire_list_spells_items(~B.Hold, ~FBg.put_hold, hs, r1),
    Equal.trans(String, LawsBase.wire_dec(n, i1), LawsBase.wire_dec(n, i2), Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, r2),
      Equal.cong(String, String, z => LawsBase.wire_dec(n, z), i1, i2, be.w_hold_items(hs, r1, r2, e)),
      Equal.sym(String, Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, r2), LawsBase.wire_dec(n, i2), Wire.wire_list_spells_items(~B.Hold, ~Budget.sp_w_hold, hs, r2))))

def be.w_acct(a: B.Acct, +r1: String, +r2: String, e: {r1 == r2 : String}) -> {FBg.put_acct(a, r1) == Budget.sp_w_acct(a, r2) : String}:
  match a:
    case B.Acct{f, s, l, o, +hs, +u}:
      -a5 = Wr.put_list(~B.Hold, ~FBg.put_hold, hs, Wr.put_nat(u, r1))
      -b5 = Wr.put_list(~B.Hold, ~Budget.sp_w_hold, hs, Wr.put_nat(u, r2))
      -a4 = FBg.put_amt(o, a5)
      -b4 = Budget.sp_w_amt(o, b5)
      -a3 = FBg.put_amt(l, a4)
      -b3 = Budget.sp_w_amt(l, b4)
      -a2 = FBg.put_amt(s, a3)
      -b2 = Budget.sp_w_amt(s, b3)
      be.w_amt(f, a2, b2, be.w_amt(s, a3, b3, be.w_amt(l, a4, b4, be.w_amt(o, a5, b5, be.w_holds(hs, Wr.put_nat(u, r1), Wr.put_nat(u, r2), Equal.cong(String, String, z => Wr.put_nat(u, z), r1, r2, e))))))

def be.w_dim(d: B.Dim, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FBg.put_dim(d, r1) == Wr.put_nat(Budget.sp_dim_tag(d), r2) : String}:
  match d:
    case B.Cost{}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), r1, r2, e)
    case B.Tok{}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), r1, r2, e)
    case B.Time{}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), r1, r2, e)
    case B.Calls{}:
      Equal.cong(String, String, z => Wr.put_nat(3n, z), r1, r2, e)
    case B.Reqs{}:
      Equal.cong(String, String, z => Wr.put_nat(4n, z), r1, r2, e)

def be.w_why(w: B.Why, -r1: String, -r2: String, e: {r1 == r2 : String}) -> {FBg.put_why(w, r1) == Budget.sp_w_why(w, r2) : String}:
  match w:
    case B.Short{d}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FBg.put_dim(d, r1), Wr.put_nat(Budget.sp_dim_tag(d), r2), be.w_dim(d, r1, r2, e))
    case B.Held{}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), r1, r2, e)
    case B.Stopped{}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), r1, r2, e)

def be.w_grant(g: B.Grant) -> {FBg.put_grant(g) == Budget.sp_w_grant(g) : String}:
  match g:
    case B.Granted{i, c, a, +t}:
      Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(i, z)), FBg.put_ask(c, FBg.put_acct(a, Wr.put_bool(t, ""))), Budget.sp_w_ask(c, Budget.sp_w_acct(a, Wr.put_bool(t, ""))),
        be.w_ask(c, FBg.put_acct(a, Wr.put_bool(t, "")), Budget.sp_w_acct(a, Wr.put_bool(t, "")), be.w_acct(a, Wr.put_bool(t, ""), Wr.put_bool(t, ""), {==})))
    case B.Refused{w, +p}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FBg.put_why(w, FBg.put_phase(p, "")), Budget.sp_w_why(w, Wr.put_nat(Budget.sp_phase_tag(p), "")),
        be.w_why(w, FBg.put_phase(p, ""), Wr.put_nat(Budget.sp_phase_tag(p), ""), be.w_phase(p, "", "", {==})))

def be.w_carve(c: B.Carve) -> {FBg.put_carve(c) == Budget.sp_w_carve(c) : String}:
  match c:
    case B.Carved{p, +k}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FBg.put_acct(p, FBg.put_acct(k, "")), Budget.sp_w_acct(p, Budget.sp_w_acct(k, "")),
        be.w_acct(p, FBg.put_acct(k, ""), Budget.sp_w_acct(k, ""), be.w_acct(k, "", "", {==})))
    case B.Kept{w}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FBg.put_why(w, ""), Budget.sp_w_why(w, ""), be.w_why(w, "", "", {==}))

def be.w_close(c: B.Close) -> {FBg.put_close(c) == Budget.sp_w_close(c) : String}:
  match c:
    case B.Closed{p, +k}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FBg.put_acct(p, FBg.put_acct(k, "")), Budget.sp_w_acct(p, Budget.sp_w_acct(k, "")),
        be.w_acct(p, FBg.put_acct(k, ""), Budget.sp_w_acct(k, ""), be.w_acct(k, "", "", {==})))
    case B.Busy{}:
      {==}

# the entry's answer is the model's decision, spelled
def be.reply(q: FBg.Req) -> {FBg.answer(q) == Budget.sp_w_reply(q) : String}:
  match q:
    case FBg.QReserve{+u, +p, +id, +now, +base, +keep, +want, less, a}:
      be.w_grant(B.reserve(u, p, id, now, base, keep, want, less, a))
    case FBg.QSettle{+id, +act, a}:
      be.w_acct(B.settle(id, act, a), "", "", {==})
    case FBg.QCarve{p, +now, +want, base, a}:
      be.w_carve(B.carve(p, now, want, base, a))
    case FBg.QClose{c, p}:
      be.w_close(B.close(c, p))
    case FBg.QFund{+n, a}:
      be.w_acct(B.fund(n, a), "", "", {==})

# No answer opens with 'E'
# ------------------------

def be.amt_ok(x: B.Amt, rest: String) -> {LawsBase.wire_opens_err(FBg.put_amt(x, rest)) == False{} : Bool}:
  match x:
    case B.Amt{c, k, n, r}:
      Wire.wire_nat_not_err(c, Wr.put_nat(k, Wr.put_nat(n, Wr.put_nat(r, rest))))

# an account opens with an amount, which opens with a Nat
def be.acct_ok(a: B.Acct, rest: String) -> {LawsBase.wire_opens_err(FBg.put_acct(a, rest)) == False{} : Bool}:
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      be.amt_ok(f, FBg.put_amt(s, FBg.put_amt(l, FBg.put_amt(o, Wr.put_list(~B.Hold, ~FBg.put_hold, hs, Wr.put_nat(u, rest))))))

def be.grant_ok(g: B.Grant) -> {LawsBase.wire_opens_err(FBg.put_grant(g)) == False{} : Bool}:
  match g:
    case B.Granted{i, c, a, t}:
      {==}
    case B.Refused{w, p}:
      {==}

def be.carve_ok(c: B.Carve) -> {LawsBase.wire_opens_err(FBg.put_carve(c)) == False{} : Bool}:
  match c:
    case B.Carved{p, k}:
      {==}
    case B.Kept{w}:
      {==}

def be.close_ok(c: B.Close) -> {LawsBase.wire_opens_err(FBg.put_close(c)) == False{} : Bool}:
  match c:
    case B.Closed{p, k}:
      {==}
    case B.Busy{}:
      {==}

# no answer opens with 'E'
def be.answer_ok(q: FBg.Req) -> {LawsBase.wire_opens_err(FBg.answer(q)) == False{} : Bool}:
  match q:
    case FBg.QReserve{u, p, id, now, base, keep, want, less, a}:
      be.grant_ok(B.reserve(u, p, id, now, base, keep, want, less, a))
    case FBg.QSettle{id, act, a}:
      be.acct_ok(B.settle(id, act, a), "")
    case FBg.QCarve{p, now, want, base, a}:
      be.carve_ok(B.carve(p, now, want, base, a))
    case FBg.QClose{c, p}:
      be.close_ok(B.close(c, p))
    case FBg.QFund{n, a}:
      be.acct_ok(B.fund(n, a), "")

# an answer that opens with 'E' is the one error form
def be.refuse(x: Wr.Dec<FBg.Req>, bad: {LawsBase.wire_opens_err(FBg.ffi.got(x)) == True{} : Bool}) -> {FBg.ffi.got(x) == Wr.err("budget: malformed request") : String}:
  match x:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          be.absurd({FBg.answer(q) == Wr.err("budget: malformed request") : String}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FBg.answer(q)), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FBg.answer(q)), False{}, be.answer_ok(q)), bad))
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}
