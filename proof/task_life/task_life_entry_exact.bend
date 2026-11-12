# eukhe: the proof of LAW task_life_entry_exact
#
# PROOF: each decoder stage of bend/ffi_task_life.bend answers Got{x,
# rest} only for an input that is the laws' spelling of x before rest
# (spec/durable/task_life_wire.bend), with every handle and count of x
# within the wire: a predicate per decoder answer (tx.*P), carried stage
# by stage with wire_nat_exact, wire_nat_decoded_fits and wire_bool_exact;
# a list's item loop tracks the items' spelling and their number, so the
# count read (which fits) is the list's length (tx.ri_*, tx.bi_*). The
# entry answers a value only for a request read whole with nothing left:
# that input is the spelled request (tx.top).

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/task_life.bend as TaskLife
import ../../spec/durable/task_life_wire.bend as SpW
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../log/base.bend as LLog
import ./base.bend as LB
import ./base/entry.bend as LE

# s is f(a), and a is b: s is f(b)
def tx.ch(-s: String, -a: String, -b: String, -f: String -> String, pre: {s == f(a) : String}, e: {a == b : String}) -> {s == f(b) : String}:
  Equal.trans(String, s, f(a), f(b), pre, Equal.cong(String, String, f, a, b, e))

# both sides of an and are true
def tx.and(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LB.tlb.absurd_ft({Bool.and(False{}, b) == True{} : Bool}, ea)

# Predicates: what a decoder's answer says about its input s
# -----------------------------------------------------------

def tx.PP(s: String, d: Wr.Dec<Tl.Policy>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == SpW.w_policy(p, r) : String}
    case Wr.Bad{}:
      Unit

def tx.ResP(s: String, d: Wr.Dec<Tl.Res>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(SpW.w_res(x), r) : String}
    case Wr.Bad{}:
      Unit

def tx.OP(s: String, d: Wr.Dec<Tl.Outcome>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == SpW.w_outcome(o, r) : String} & {SpW.fit_outcome(o) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.SP(s: String, d: Wr.Dec<Tl.St>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == SpW.w_st(x, r) : String} & {SpW.fit_st(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.NP(s: String, d: Wr.Dec<Tl.Next>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == SpW.w_next(n, r) : String} & {SpW.fit_next(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.EP(s: String, d: Wr.Dec<Tl.Ev>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == SpW.w_ev(e, r) : String} & {SpW.fit_ev(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.MP(s: String, d: Wr.Dec<Tl.Mark>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == SpW.w_mark(m, r) : String}
    case Wr.Bad{}:
      Unit

def tx.RowP(s: String, d: Wr.Dec<Tl.Row>) -> Type:
  match d:
    case Wr.Got{w, r}:
      {s == SpW.w_row(w, r) : String}
    case Wr.Bad{}:
      Unit

def tx.LP(s: String, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == SpW.w_bools(xs, r) : String} & {LawsBase.wire_fits(List.length(&2, Bool, xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.RsP(s: String, d: Wr.Dec<List<&2, Tl.Row>>) -> Type:
  match d:
    case Wr.Got{rs, r}:
      {s == Wr.put_list(~Tl.Row, ~SpW.w_row, rs, r) : String} & {LawsBase.wire_fits(List.length(&2, Tl.Row, rs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.RP(s: String, d: Wr.Dec<FTl.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == SpW.w_req(q, r) : String} & {SpW.fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# Tags
# ----

def tx.policy(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.PP(s, FTl.get_policy(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, ed)
        case 2n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.res(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.ResP(s, FTl.get_res(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s1, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s1, ed)
        case 4n:
          Wire.wire_nat_exact(s, 4n, s1, ed)
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.mark(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.MP(s, FTl.get_mark(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s1, ed)
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# Outcomes
# --------

def tx.out_h(-s: String, +x: Tl.Res, +s1: String, pre: {s == Wr.put_nat(SpW.w_res(x), s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.OP(s, FTl.get_outcome.h(x, d)):
  match d:
    case Wr.Got{+h, +r}:
      +e = ed
      (tx.ch(s, s1, Wr.put_nat(h, r), z => Wr.put_nat(SpW.w_res(x), z), pre, Wire.wire_nat_exact(s1, h, r, e)), Wire.wire_nat_decoded_fits(s1, h, r, e))
    case Wr.Bad{}:
      Unit{}

def tx.out_r(-s: String, d: Wr.Dec<Tl.Res>, rp: tx.ResP(s, d)) -> tx.OP(s, FTl.get_outcome(d)):
  match d:
    case Wr.Got{+x, +s1}:
      tx.out_h(s, x, s1, rp, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# an outcome decoded at s is spelled there, and fits
def tx.outcome(+s: String) -> tx.OP(s, FTl.get_outcome(FTl.get_res(Wr.get_nat(s)))):
  tx.out_r(s, FTl.get_res(Wr.get_nat(s)), tx.res(s, Wr.get_nat(s), {==}))

# States
# ------

def tx.st_pend(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.SP(s, FTl.get_st.one(d, 0n)):
  match d:
    case Wr.Got{+c, +r}:
      +e = ed
      (tx.ch(s, s1, Wr.put_nat(c, r), z => Wr.put_nat(0n, z), pre, Wire.wire_nat_exact(s1, c, r, e)), Wire.wire_nat_decoded_fits(s1, c, r, e))
    case Wr.Bad{}:
      Unit{}

def tx.st_run(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.SP(s, FTl.get_st.one(d, 1n)):
  match d:
    case Wr.Got{+c, +r}:
      +e = ed
      (tx.ch(s, s1, Wr.put_nat(c, r), z => Wr.put_nat(1n, z), pre, Wire.wire_nat_exact(s1, c, r, e)), Wire.wire_nat_decoded_fits(s1, c, r, e))
    case Wr.Bad{}:
      Unit{}

def tx.st_pol(-s: String, +c: Nat, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(c, s2)) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Tl.Policy>, pp: tx.PP(s2, d)) -> tx.SP(s, FTl.get_st.policy(c, d)):
  match d:
    case Wr.Got{+p, +r}:
      (tx.ch(s, s2, SpW.w_policy(p, r), z => Wr.put_nat(2n, Wr.put_nat(c, z)), pre, pp), fc)
    case Wr.Bad{}:
      Unit{}

def tx.st_wait(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.SP(s, FTl.get_st.wait(d)):
  match d:
    case Wr.Got{+c, +s2}:
      +e = ed
      tx.st_pol(s, c, s2, tx.ch(s, s1, Wr.put_nat(c, s2), z => Wr.put_nat(2n, z), pre, Wire.wire_nat_exact(s1, c, s2, e)), Wire.wire_nat_decoded_fits(s1, c, s2, e), FTl.get_policy(Wr.get_nat(s2)), tx.policy(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.st_held(-s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Tl.Outcome>, op: tx.OP(s1, d)) -> tx.SP(s, FTl.get_st.out(d, 0n)):
  match d:
    case Wr.Got{+o, +r}:
      (e1, f) = op
      (tx.ch(s, s1, SpW.w_outcome(o, r), z => Wr.put_nat(3n, z), pre, e1), f)
    case Wr.Bad{}:
      Unit{}

def tx.st_end(-s: String, +s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Tl.Outcome>, op: tx.OP(s1, d)) -> tx.SP(s, FTl.get_st.out(d, 1n)):
  match d:
    case Wr.Got{+o, +r}:
      (e1, f) = op
      (tx.ch(s, s1, SpW.w_outcome(o, r), z => Wr.put_nat(4n, z), pre, e1), f)
    case Wr.Bad{}:
      Unit{}

def tx.st(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.SP(s, FTl.get_st(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          tx.st_pend(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_nat(s1), {==})
        case 1n:
          tx.st_run(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_nat(s1), {==})
        case 2n:
          tx.st_wait(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_nat(s1), {==})
        case 3n:
          tx.st_held(s, s1, Wire.wire_nat_exact(s, 3n, s1, ed), FTl.get_outcome(FTl.get_res(Wr.get_nat(s1))), tx.outcome(s1))
        case 4n:
          tx.st_end(s, s1, Wire.wire_nat_exact(s, 4n, s1, ed), FTl.get_outcome(FTl.get_res(Wr.get_nat(s1))), tx.outcome(s1))
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# Next states
# -----------

def tx.nx_run(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.NP(s, FTl.get_next.run(d)):
  match d:
    case Wr.Got{+c, +r}:
      +e = ed
      (tx.ch(s, s1, Wr.put_nat(c, r), z => Wr.put_nat(0n, z), pre, Wire.wire_nat_exact(s1, c, r, e)), Wire.wire_nat_decoded_fits(s1, c, r, e))
    case Wr.Bad{}:
      Unit{}

def tx.nx_pol(-s: String, +c: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(c, s2)) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Tl.Policy>, pp: tx.PP(s2, d)) -> tx.NP(s, FTl.get_next.policy(c, d)):
  match d:
    case Wr.Got{+p, +r}:
      (tx.ch(s, s2, SpW.w_policy(p, r), z => Wr.put_nat(1n, Wr.put_nat(c, z)), pre, pp), fc)
    case Wr.Bad{}:
      Unit{}

def tx.nx_wait(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> tx.NP(s, FTl.get_next.wait(d)):
  match d:
    case Wr.Got{+c, +s2}:
      +e = ed
      tx.nx_pol(s, c, s2, tx.ch(s, s1, Wr.put_nat(c, s2), z => Wr.put_nat(1n, z), pre, Wire.wire_nat_exact(s1, c, s2, e)), Wire.wire_nat_decoded_fits(s1, c, s2, e), FTl.get_policy(Wr.get_nat(s2)), tx.policy(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.nx_end(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Tl.Outcome>, op: tx.OP(s1, d)) -> tx.NP(s, FTl.get_next.end(d)):
  match d:
    case Wr.Got{+o, +r}:
      (e1, f) = op
      (tx.ch(s, s1, SpW.w_outcome(o, r), z => Wr.put_nat(2n, z), pre, e1), f)
    case Wr.Bad{}:
      Unit{}

def tx.next(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.NP(s, FTl.get_next(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          tx.nx_run(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_nat(s1), {==})
        case 1n:
          tx.nx_wait(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_nat(s1), {==})
        case 2n:
          tx.nx_end(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), FTl.get_outcome(FTl.get_res(Wr.get_nat(s1))), tx.outcome(s1))
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# Transitions
# -----------

def tx.ev_commit_h(-s: String, +n: Tl.Next, +s2: String, pre: {s == Wr.put_nat(1n, SpW.w_next(n, s2)) : String}, fn: {SpW.fit_next(n) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> tx.EP(s, FTl.get_ev.commit_h(n, d)):
  match d:
    case Wr.Got{+h, +r}:
      (tx.ch(s, s2, Wr.put_bool(h, r), z => Wr.put_nat(1n, SpW.w_next(n, z)), pre, Wire.wire_bool_exact(s2, h, r, ed)), fn)
    case Wr.Bad{}:
      Unit{}

def tx.ev_commit(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Tl.Next>, np: tx.NP(s1, d)) -> tx.EP(s, FTl.get_ev.commit(d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e1, f) = np
      tx.ev_commit_h(s, n, s2, tx.ch(s, s1, SpW.w_next(n, s2), z => Wr.put_nat(1n, z), pre, e1), f, Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def tx.ev_settle_h(-s: String, +o: Tl.Outcome, +s2: String, pre: {s == Wr.put_nat(3n, SpW.w_outcome(o, s2)) : String}, fo: {SpW.fit_outcome(o) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> tx.EP(s, FTl.get_ev.settle_h(o, d)):
  match d:
    case Wr.Got{+h, +r}:
      (tx.ch(s, s2, Wr.put_bool(h, r), z => Wr.put_nat(3n, SpW.w_outcome(o, z)), pre, Wire.wire_bool_exact(s2, h, r, ed)), fo)
    case Wr.Bad{}:
      Unit{}

def tx.ev_settle(-s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Tl.Outcome>, op: tx.OP(s1, d)) -> tx.EP(s, FTl.get_ev.settle(d)):
  match d:
    case Wr.Got{+o, +s2}:
      (e1, f) = op
      tx.ev_settle_h(s, o, s2, tx.ch(s, s1, SpW.w_outcome(o, s2), z => Wr.put_nat(3n, z), pre, e1), f, Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def tx.ev_fin(-s: String, +s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> tx.EP(s, FTl.get_ev.fin(d)):
  match d:
    case Wr.Got{+h, +r}:
      (tx.ch(s, s1, Wr.put_bool(h, r), z => Wr.put_nat(4n, z), pre, Wire.wire_bool_exact(s1, h, r, ed)), {==})
    case Wr.Bad{}:
      Unit{}

def tx.ev(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.EP(s, FTl.get_ev(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, ed), {==})
        case 1n:
          tx.ev_commit(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), FTl.get_next(Wr.get_nat(s1)), tx.next(s1, Wr.get_nat(s1), {==}))
        case 2n:
          (Wire.wire_nat_exact(s, 2n, s1, ed), {==})
        case 3n:
          tx.ev_settle(s, s1, Wire.wire_nat_exact(s, 3n, s1, ed), FTl.get_outcome(FTl.get_res(Wr.get_nat(s1))), tx.outcome(s1))
        case 4n:
          tx.ev_fin(s, s1, Wire.wire_nat_exact(s, 4n, s1, ed), Wr.get_bool(s1), {==})
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# Rows
# ----

def tx.row_mark(-s: String, +l: Bool, +b: Bool, +s2: String, pre: {s == Wr.put_bool(l, Wr.put_bool(b, s2)) : String}, d: Wr.Dec<Tl.Mark>, mp: tx.MP(s2, d)) -> tx.RowP(s, FTl.get_row.mark(l, b, d)):
  match d:
    case Wr.Got{+m, +r}:
      tx.ch(s, s2, SpW.w_mark(m, r), z => Wr.put_bool(l, Wr.put_bool(b, z)), pre, mp)
    case Wr.Bad{}:
      Unit{}

def tx.row_bg(-s: String, +l: Bool, +s1: String, pre: {s == Wr.put_bool(l, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> tx.RowP(s, FTl.get_row.bg(l, d)):
  match d:
    case Wr.Got{+b, +s2}:
      tx.row_mark(s, l, b, s2, tx.ch(s, s1, Wr.put_bool(b, s2), z => Wr.put_bool(l, z), pre, Wire.wire_bool_exact(s1, b, s2, ed)), FTl.get_mark(Wr.get_nat(s2)), tx.mark(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.row_live(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> tx.RowP(s, FTl.get_row.live(d)):
  match d:
    case Wr.Got{+l, +s1}:
      tx.row_bg(s, l, s1, Wire.wire_bool_exact(s, l, s1, ed), Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

def tx.row_at(+s: String, -d: Wr.Dec<Tl.Row>, ed: {FTl.get_row(s) == d : Wr.Dec<Tl.Row>}) -> tx.RowP(s, d):
  %ed : tx.RowP(s, _)
  tx.row_live(s, Wr.get_bool(s), {==})

# the item loop over m + 1 rows: their spelling, and how many
def tx.RI(s: String, m: Nat, d: Wr.Dec<List<&2, Tl.Row>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LE.tle.items(xs, r) : String} & {List.length(&2, Tl.Row, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def tx.ri_step(-s: String, +x: Tl.Row, +s3: String, -k: Nat, ex: {s == SpW.w_row(x, s3) : String}, d: Wr.Dec<List<&2, Tl.Row>>, ih: tx.RI(s3, k, d)) -> tx.RI(s, 1n+k, Wr.get_list.cons(Tl.Row, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (tx.ch(s, s3, LE.tle.items(ys, r), z => SpW.w_row(x, z), ex, e1), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Tl.Row, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

def tx.ri_spec(m: Nat, cur: Wr.Dec<Tl.Row>, +s: String, er: {FTl.get_row(s) == cur : Wr.Dec<Tl.Row>}) -> tx.RI(s, m, Wr.get_list.go(~Tl.Row, ~FTl.get_row, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (tx.row_at(s, Wr.Got{x, s3}, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      tx.ri_step(s, x, s3, k, tx.row_at(s, Wr.Got{x, s3}, er), Wr.get_list.go(~Tl.Row, ~FTl.get_row, k, FTl.get_row(s3)), tx.ri_spec(k, FTl.get_row(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

def tx.rs_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Tl.Row>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LE.tle.items(xs, r) : String}, e2: {List.length(&2, Tl.Row, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Tl.Row, ~SpW.w_row, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Tl.Row, ~SpW.w_row, xs, r), Wr.put_nat(List.length(&2, Tl.Row, xs), LE.tle.items(xs, r)), LE.tle.put_rows(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Tl.Row, xs), 1n+m, e2) : {s == Wr.put_nat(_, LE.tle.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def tx.rs_conv(-s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Tl.Row>>, ri: tx.RI(s2, m, d)) -> tx.RsP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = ri
      +f = fm
      (tx.rs_eq(s, s2, m, xs, r, en, e1, e2), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Tl.Row, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), List.length(&2, Tl.Row, xs), 1n+m, e2), f))
    case Wr.Bad{}:
      Unit{}

def tx.rs_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> tx.RsP(s, Wr.get_list.start(~Tl.Row, ~FTl.get_row, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, fn)
    case 1n++m:
      tx.rs_conv(s, s2, m, en, fn, Wr.get_list.go(~Tl.Row, ~FTl.get_row, m, FTl.get_row(s2)), tx.ri_spec(m, FTl.get_row(s2), s2, {==}))

def tx.rs_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> tx.RsP(s, Wr.get_list.start(~Tl.Row, ~FTl.get_row, r)):
  match r:
    case Wr.Got{+n, +s2}:
      +e = er
      tx.rs_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of rows decoded at s is spelled there, and its count fits
def tx.rows(+s: String) -> tx.RsP(s, Wr.get_list(~Tl.Row, ~FTl.get_row, s)):
  tx.rs_top(s, Wr.get_nat(s), {==})

# Lists of flags
# --------------

def tx.BI(s: String, m: Nat, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LLog.pe.bools(xs, r) : String} & {List.length(&2, Bool, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def tx.bi_step(-s: String, +x: Bool, +s3: String, -k: Nat, ex: {s == Wr.put_bool(x, s3) : String}, d: Wr.Dec<List<&2, Bool>>, ih: tx.BI(s3, k, d)) -> tx.BI(s, 1n+k, Wr.get_list.cons(Bool, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (tx.ch(s, s3, LLog.pe.bools(ys, r), z => Wr.put_bool(x, z), ex, e1), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Bool, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

def tx.bi_spec(m: Nat, cur: Wr.Dec<Bool>, +s: String, er: {Wr.get_bool(s) == cur : Wr.Dec<Bool>}) -> tx.BI(s, m, Wr.get_list.go(~Bool, ~Wr.get_bool, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (Wire.wire_bool_exact(s, x, s3, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      tx.bi_step(s, x, s3, k, Wire.wire_bool_exact(s, x, s3, er), Wr.get_list.go(~Bool, ~Wr.get_bool, k, Wr.get_bool(s3)), tx.bi_spec(k, Wr.get_bool(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

def tx.bs_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Bool>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == LLog.pe.bools(xs, r) : String}, e2: {List.length(&2, Bool, xs) == 1n+m : Nat}) -> {s == SpW.w_bools(xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Bool, ~Wr.put_bool, xs, r), Wr.put_nat(List.length(&2, Bool, xs), LLog.pe.bools(xs, r)), LLog.pe.put_list(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Bool, xs), 1n+m, e2) : {s == Wr.put_nat(_, LLog.pe.bools(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def tx.bs_conv(-s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, bi: tx.BI(s2, m, d)) -> tx.LP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = bi
      +f = fm
      (tx.bs_eq(s, s2, m, xs, r, en, e1, e2), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Bool, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), List.length(&2, Bool, xs), 1n+m, e2), f))
    case Wr.Bad{}:
      Unit{}

def tx.bs_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> tx.LP(s, Wr.get_list.start(~Bool, ~Wr.get_bool, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, fn)
    case 1n++m:
      tx.bs_conv(s, s2, m, en, fn, Wr.get_list.go(~Bool, ~Wr.get_bool, m, Wr.get_bool(s2)), tx.bi_spec(m, Wr.get_bool(s2), s2, {==}))

def tx.bs_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> tx.LP(s, Wr.get_list.start(~Bool, ~Wr.get_bool, r)):
  match r:
    case Wr.Got{+n, +s2}:
      +e = er
      tx.bs_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of flags decoded at s is spelled there, and its count fits
def tx.bools(+s: String) -> tx.LP(s, Wr.get_list(~Bool, ~Wr.get_bool, s)):
  tx.bs_top(s, Wr.get_nat(s), {==})

# Requests
# --------

def tx.step_e(-s: String, +x: Tl.St, +s2: String, pre: {s == Wr.put_nat(0n, SpW.w_st(x, s2)) : String}, fx: {SpW.fit_st(x) == True{} : Bool}, d: Wr.Dec<Tl.Ev>, ep: tx.EP(s2, d)) -> tx.RP(s, FTl.get_req.step_e(x, d)):
  match d:
    case Wr.Got{+e, +r}:
      (e1, fe) = ep
      (tx.ch(s, s2, SpW.w_ev(e, r), z => Wr.put_nat(0n, SpW.w_st(x, z)), pre, e1), tx.and(SpW.fit_st(x), SpW.fit_ev(e), fx, fe))
    case Wr.Bad{}:
      Unit{}

def tx.step(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Tl.St>, sp: tx.SP(s1, d)) -> tx.RP(s, FTl.get_req.step(d)):
  match d:
    case Wr.Got{+x, +s2}:
      (e1, fx) = sp
      tx.step_e(s, x, s2, tx.ch(s, s1, SpW.w_st(x, s2), z => Wr.put_nat(0n, z), pre, e1), fx, FTl.get_ev(Wr.get_nat(s2)), tx.ev(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.resume(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Tl.St>, sp: tx.SP(s1, d)) -> tx.RP(s, FTl.get_req.resume(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e1, fx) = sp
      (tx.ch(s, s1, SpW.w_st(x, r), z => Wr.put_nat(1n, z), pre, e1), fx)
    case Wr.Bad{}:
      Unit{}

def tx.join_f(-s: String, +p: Tl.Policy, +ls: List<&2, Bool>, +s3: String, pre: {s == Wr.put_nat(2n, SpW.w_policy(p, SpW.w_bools(ls, s3))) : String}, fl: {LawsBase.wire_fits(List.length(&2, Bool, ls)) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, lp: tx.LP(s3, d)) -> tx.RP(s, FTl.get_req.join_f(p, ls, d)):
  match d:
    case Wr.Got{+fs, +r}:
      (e1, ff) = lp
      (tx.ch(s, s3, SpW.w_bools(fs, r), z => Wr.put_nat(2n, SpW.w_policy(p, SpW.w_bools(ls, z))), pre, e1), tx.and(LawsBase.wire_fits(List.length(&2, Bool, ls)), LawsBase.wire_fits(List.length(&2, Bool, fs)), fl, ff))
    case Wr.Bad{}:
      Unit{}

def tx.join_l(-s: String, +p: Tl.Policy, +s2: String, pre: {s == Wr.put_nat(2n, SpW.w_policy(p, s2)) : String}, d: Wr.Dec<List<&2, Bool>>, lp: tx.LP(s2, d)) -> tx.RP(s, FTl.get_req.join_l(p, d)):
  match d:
    case Wr.Got{+ls, +s3}:
      (e1, fl) = lp
      tx.join_f(s, p, ls, s3, tx.ch(s, s2, SpW.w_bools(ls, s3), z => Wr.put_nat(2n, SpW.w_policy(p, z)), pre, e1), fl, Wr.get_list(~Bool, ~Wr.get_bool, s3), tx.bools(s3))
    case Wr.Bad{}:
      Unit{}

def tx.join(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Tl.Policy>, pp: tx.PP(s1, d)) -> tx.RP(s, FTl.get_req.join(d)):
  match d:
    case Wr.Got{+p, +s2}:
      tx.join_l(s, p, s2, tx.ch(s, s1, SpW.w_policy(p, s2), z => Wr.put_nat(2n, z), pre, pp), Wr.get_list(~Bool, ~Wr.get_bool, s2), tx.bools(s2))
    case Wr.Bad{}:
      Unit{}

def tx.merge_b(-s: String, +a: Tl.Mark, +s2: String, pre: {s == Wr.put_nat(3n, SpW.w_mark(a, s2)) : String}, d: Wr.Dec<Tl.Mark>, mp: tx.MP(s2, d)) -> tx.RP(s, FTl.get_req.merge_b(a, d)):
  match d:
    case Wr.Got{+b, +r}:
      (tx.ch(s, s2, SpW.w_mark(b, r), z => Wr.put_nat(3n, SpW.w_mark(a, z)), pre, mp), {==})
    case Wr.Bad{}:
      Unit{}

def tx.merge(-s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Tl.Mark>, mp: tx.MP(s1, d)) -> tx.RP(s, FTl.get_req.merge(d)):
  match d:
    case Wr.Got{+a, +s2}:
      tx.merge_b(s, a, s2, tx.ch(s, s1, SpW.w_mark(a, s2), z => Wr.put_nat(3n, z), pre, mp), FTl.get_mark(Wr.get_nat(s2)), tx.mark(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.cas_r(-s: String, +x: Tl.St, +m: Tl.Mark, +s3: String, pre: {s == Wr.put_nat(4n, SpW.w_st(x, SpW.w_mark(m, s3))) : String}, fx: {SpW.fit_st(x) == True{} : Bool}, d: Wr.Dec<List<&2, Tl.Row>>, rp: tx.RsP(s3, d)) -> tx.RP(s, FTl.get_req.cascade_r(x, m, d)):
  match d:
    case Wr.Got{+rs, +r}:
      (e1, fr) = rp
      (tx.ch(s, s3, Wr.put_list(~Tl.Row, ~SpW.w_row, rs, r), z => Wr.put_nat(4n, SpW.w_st(x, SpW.w_mark(m, z))), pre, e1), tx.and(SpW.fit_st(x), LawsBase.wire_fits(List.length(&2, Tl.Row, rs)), fx, fr))
    case Wr.Bad{}:
      Unit{}

def tx.cas_m(-s: String, +x: Tl.St, +s2: String, pre: {s == Wr.put_nat(4n, SpW.w_st(x, s2)) : String}, fx: {SpW.fit_st(x) == True{} : Bool}, d: Wr.Dec<Tl.Mark>, mp: tx.MP(s2, d)) -> tx.RP(s, FTl.get_req.cascade_m(x, d)):
  match d:
    case Wr.Got{+m, +s3}:
      tx.cas_r(s, x, m, s3, tx.ch(s, s2, SpW.w_mark(m, s3), z => Wr.put_nat(4n, SpW.w_st(x, z)), pre, mp), fx, Wr.get_list(~Tl.Row, ~FTl.get_row, s3), tx.rows(s3))
    case Wr.Bad{}:
      Unit{}

def tx.cascade(-s: String, +s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Tl.St>, sp: tx.SP(s1, d)) -> tx.RP(s, FTl.get_req.cascade(d)):
  match d:
    case Wr.Got{+x, +s2}:
      (e1, fx) = sp
      tx.cas_m(s, x, s2, tx.ch(s, s1, SpW.w_st(x, s2), z => Wr.put_nat(4n, z), pre, e1), fx, FTl.get_mark(Wr.get_nat(s2)), tx.mark(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def tx.req(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.RP(s, FTl.get_req(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          tx.step(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), FTl.get_st(Wr.get_nat(s1)), tx.st(s1, Wr.get_nat(s1), {==}))
        case 1n:
          tx.resume(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), FTl.get_st(Wr.get_nat(s1)), tx.st(s1, Wr.get_nat(s1), {==}))
        case 2n:
          tx.join(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), FTl.get_policy(Wr.get_nat(s1)), tx.policy(s1, Wr.get_nat(s1), {==}))
        case 3n:
          tx.merge(s, s1, Wire.wire_nat_exact(s, 3n, s1, ed), FTl.get_mark(Wr.get_nat(s1)), tx.mark(s1, Wr.get_nat(s1), {==}))
        case 4n:
          tx.cascade(s, s1, Wire.wire_nat_exact(s, 4n, s1, ed), FTl.get_st(Wr.get_nat(s1)), tx.st(s1, Wr.get_nat(s1), {==}))
        case 5n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def tx.G(s: String) -> Type:
  Sigma<&1, &1, FTl.Req, q => {s == SpW.w_req(q, "") : String} & {SpW.fit_req(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def tx.top(-s: String, d: Wr.Dec<FTl.Req>, rp: tx.RP(s, d), ok: {LawsBase.wire_opens_err(FTl.ffi.got(d)) == False{} : Bool}) -> tx.G(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LB.tlb.absurd_tf(tx.G(s), ok)
    case Wr.Bad{}:
      LB.tlb.absurd_tf(tx.G(s), ok)

def TaskLife.task_life_entry_exact(s, ok):
  tx.top(s, FTl.get_req(Wr.get_nat(s)), tx.req(s, Wr.get_nat(s), {==}), ok)
