# eukhe: lemmas the proofs of area child share

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_eq.bend as LNatIsEq
import ../base/nat/is_le.bend as LNatIsLe
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def pc.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.child.pc.absurd({False{} == True{} : Bool}, e)

def pc.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LBoolMisc.child.pc.absurd({b == True{} : Bool}, e)

def pc.and_in(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LBoolMisc.child.pc.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

def pc.le_of_eq(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.child.pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_of_eq(p, q, e)

def pc.le_pred(+a: Nat, +b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      LNatIsLe.child.pc.le_zero(b)
    case 1n+p 0n:
      LBoolMisc.child.pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_pred(p, q, e)

def pc.isW(f: Ch.Fate) -> Bool:
  match f:
    case Ch.Queued{}:
      False{}
    case Ch.Withdrawn{}:
      True{}
    case Ch.Placed{}:
      False{}

def pc.empty(inbox: List<&2, Ch.Sub>) -> Bool:
  match inbox:
    case Nil{}:
      True{}
    case s <> rest:
      False{}

# every submission in rest is withdrawn, under an id below m (newest
# first)
def pc.Old(rest: List<&2, Ch.Sub>, +m: Nat) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case s <> r:
      match s:
        case Ch.Sub{+j, f}:
          Bool.and(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)))

# every submission but the newest is withdrawn
def pc.Kin(inbox: List<&2, Ch.Sub>) -> Bool:
  match inbox:
    case Nil{}:
      True{}
    case s <> rest:
      match s:
        case Ch.Sub{+m, f}:
          pc.Old(rest, m)

# owing id n: the newest submission has id n (same), or id n - 1 and is
# withdrawn
def pc.Kowe.at(same: Bool, +n: Nat, +m: Nat, f: Ch.Fate) -> Bool:
  match same:
    case True{}:
      True{}
    case False{}:
      Bool.and(Nat.is_eq(1n+m, n), pc.isW(f))

# owing id n: no submission yet (and n is 1), or as Kowe.at
def pc.Kowe(inbox: List<&2, Ch.Sub>, +n: Nat) -> Bool:
  match inbox:
    case Nil{}:
      Nat.is_eq(n, 1n)
    case s <> rest:
      match s:
        case Ch.Sub{+m, f}:
          pc.Kowe.at(Nat.is_eq(m, n), n, m, f)

def pc.Kph(ph: Ch.Ph, inbox: List<&2, Ch.Sub>) -> Bool:
  match ph:
    case Ch.Watching{w}:
      pc.empty(inbox)
    case Ch.Owing{k, +n}:
      pc.Kowe(inbox, n)
    case Ch.Ended{}:
      True{}

def pc.K(s: Ch.St) -> Bool:
  match s:
    case Ch.St{ph, cut, open, +inbox}:
      Bool.and(pc.Kph(ph, inbox), pc.Kin(inbox))

def pc.Kin_of(s: Ch.St, k: {pc.K(s) == True{} : Bool}) -> {pc.Kin(Ch.St.inbox(s)) == True{} : Bool}:
  match s:
    case Ch.St{ph, cut, open, +inbox}:
      pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k)

# the parts of Old(Sub{j, f} <> r, m)
def pc.old_head(+f: Ch.Fate, +j: Nat, +m: Nat, +r: List<&2, Ch.Sub>, o: {pc.Old(Ch.Sub{j, f} <> r, m) == True{} : Bool}) -> {pc.isW(f) == True{} : Bool}:
  pc.and_l(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)), o)

def pc.old_lt(+f: Ch.Fate, +j: Nat, +m: Nat, +r: List<&2, Ch.Sub>, o: {pc.Old(Ch.Sub{j, f} <> r, m) == True{} : Bool}) -> {Nat.is_le(1n+j, m) == True{} : Bool}:
  pc.and_l(Nat.is_le(1n+j, m), pc.Old(r, j), pc.and_r(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)), o))

def pc.old_tail(+f: Ch.Fate, +j: Nat, +m: Nat, +r: List<&2, Ch.Sub>, o: {pc.Old(Ch.Sub{j, f} <> r, m) == True{} : Bool}) -> {pc.Old(r, j) == True{} : Bool}:
  pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), pc.and_r(pc.isW(f), Bool.and(Nat.is_le(1n+j, m), pc.Old(r, j)), o))

# no submission in an old list has an id m or above
def pc.old_none.at(same: Bool, +j: Nat, +n: Nat, -f: Ch.Fate, -r: List<&2, Ch.Sub>, eb: {Nat.is_eq(j, n) == same : Bool}, lt: {Nat.is_le(1n+j, n) == True{} : Bool}, ih: {None{} == Ch.fate(r, n) : Maybe<&2, Ch.Fate>}) -> {None{} == Maybe.or(&2, Ch.Fate, Ch.fate.here(same, f), Ch.fate(r, n)) : Maybe<&2, Ch.Fate>}:
  match same:
    case True{}:
      LNatIsLe.pc.lt_ne({None{} == Some{f} : Maybe<&2, Ch.Fate>}, j, n, lt, eb)
    case False{}:
      ih

def pc.old_none(rest: List<&2, Ch.Sub>, +m: Nat, +n: Nat, +o: {pc.Old(rest, m) == True{} : Bool}, +le: {Nat.is_le(m, n) == True{} : Bool}) -> {None{} == Ch.fate(rest, n) : Maybe<&2, Ch.Fate>}:
  match rest:
    case Nil{}:
      {==}
    case s <> +r:
      match s:
        case Ch.Sub{+j, +f}:
          pc.old_none.at(Nat.is_eq(j, n), j, n, f, r, {==}, LNatIsLe.child.pc.le_trans(1n+j, m, n, pc.old_lt(f, j, m, r, o), le), pc.old_none(r, j, n, pc.old_tail(f, j, m, r, o), pc.le_pred(j, n, LNatIsLe.child.pc.le_trans(1n+j, m, n, pc.old_lt(f, j, m, r, o), le))))

# no submission in an old list is placed or live
def pc.old_placed(rest: List<&2, Ch.Sub>, +m: Nat, o: {pc.Old(rest, m) == True{} : Bool}) -> {0n == Ch.placed(rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case Ch.Sub{+j, f}:
          match f:
            case Ch.Queued{}:
              LBoolMisc.child.pc.absurd({0n == Ch.placed(Ch.Sub{j, Ch.Queued{}} <> r) : Nat}, o)
            case Ch.Withdrawn{}:
              pc.old_placed(r, j, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o))
            case Ch.Placed{}:
              LBoolMisc.child.pc.absurd({0n == Ch.placed(Ch.Sub{j, Ch.Placed{}} <> r) : Nat}, o)

# a delivery or withdrawal leaves a withdrawn submission withdrawn
def pc.isW_act(f: Ch.Fate, +a: Ch.Act, +i: Nat, w: {pc.isW(f) == True{} : Bool}) -> {pc.isW(Ch.Fate.act(a, i, f)) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      LBoolMisc.child.pc.absurd({pc.isW(Ch.Fate.act(a, i, Ch.Queued{})) == True{} : Bool}, w)
    case Ch.Withdrawn{}:
      {==}
    case Ch.Placed{}:
      LBoolMisc.child.pc.absurd({pc.isW(Ch.Fate.act(a, i, Ch.Placed{})) == True{} : Bool}, w)

def pc.old_act(rest: List<&2, Ch.Sub>, +m: Nat, +a: Ch.Act, +o: {pc.Old(rest, m) == True{} : Bool}) -> {pc.Old(Ch.act(rest, a), m) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case s <> +r:
      match s:
        case Ch.Sub{+j, +f}:
          pc.and_in(pc.isW(Ch.Fate.act(a, j, f)), Bool.and(Nat.is_le(1n+j, m), pc.Old(Ch.act(r, a), j)), pc.isW_act(f, a, j, pc.old_head(f, j, m, r, o)), pc.and_in(Nat.is_le(1n+j, m), pc.Old(Ch.act(r, a), j), pc.old_lt(f, j, m, r, o), pc.old_act(r, j, a, pc.old_tail(f, j, m, r, o))))

# The invariant K

def pc.kat(same: Bool, +n: Nat, +m: Nat, -f: Ch.Fate, e: {same == True{} : Bool}) -> {pc.Kowe.at(same, n, m, f) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.child.pc.absurd({pc.Kowe.at(False{}, n, m, f) == True{} : Bool}, e)

# after the newest submission n is withdrawn, the task owes n + 1
def pc.kat_w(same: Bool, +m: Nat, +n: Nat, e: {Nat.is_eq(m, n) == True{} : Bool}) -> {pc.Kowe.at(same, 1n+n, m, Ch.Withdrawn{}) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      pc.and_in(Nat.is_eq(1n+m, 1n+n), True{}, e, {==})

def pc.kat_act(same: Bool, +n: Nat, +m: Nat, +f: Ch.Fate, +a: Ch.Act, +k: {pc.Kowe.at(same, n, m, f) == True{} : Bool}) -> {pc.Kowe.at(same, n, m, Ch.Fate.act(a, m, f)) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      pc.and_in(Nat.is_eq(1n+m, n), pc.isW(Ch.Fate.act(a, m, f)), pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), k), pc.isW_act(f, a, m, pc.and_r(Nat.is_eq(1n+m, n), pc.isW(f), k)))

# the watch hands on no submission
def pc.Kph_watched(x: Ch.Next) -> {pc.Kph(Ch.watched(x), Nil{}) == True{} : Bool}:
  match x:
    case Ch.Watch{w}:
      {==}
    case Ch.Owe{k}:
      {==}
    case Ch.Quiet{}:
      {==}

# the first submission
def pc.K_new0(open: Bool, +kr: Ch.Report, +n: Nat, kph: {Nat.is_eq(n, 1n) == True{} : Bool}) -> {pc.K(Ch.owe.new(open, kr, n, Nil{})) == True{} : Bool}:
  match open:
    case True{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, Ch.Queued{}), True{}, pc.kat(Nat.is_eq(n, n), n, n, Ch.Queued{}, LNatIsEq.child.pc.eq_refl(n)), {==})
    case False{}:
      pc.and_in(Nat.is_eq(n, 1n), True{}, kph, {==})

# a submission after the withdrawn one m
def pc.K_new(open: Bool, +kr: Ch.Report, +n: Nat, +m: Nat, +f: Ch.Fate, +rest: List<&2, Ch.Sub>, +kph: {Bool.and(Nat.is_eq(1n+m, n), pc.isW(f)) == True{} : Bool}, kph0: {pc.Kowe.at(Nat.is_eq(m, n), n, m, f) == True{} : Bool}, kin: {pc.Old(rest, m) == True{} : Bool}) -> {pc.K(Ch.owe.new(open, kr, n, Ch.Sub{m, f} <> rest)) == True{} : Bool}:
  match open:
    case True{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, Ch.Queued{}), pc.Old(Ch.Sub{m, f} <> rest, n), pc.kat(Nat.is_eq(n, n), n, n, Ch.Queued{}, LNatIsEq.child.pc.eq_refl(n)), pc.and_in(pc.isW(f), Bool.and(Nat.is_le(1n+m, n), pc.Old(rest, m)), pc.and_r(Nat.is_eq(1n+m, n), pc.isW(f), kph), pc.and_in(Nat.is_le(1n+m, n), pc.Old(rest, m), pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)), kin)))
    case False{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, f), pc.Old(rest, m), kph0, kin)

# the report rule on the newest submission m (same: m is the owed id n)
def pc.K_owe.at(same: Bool, +kr: Ch.Report, +n: Nat, +m: Nat, f: Ch.Fate, +rest: List<&2, Ch.Sub>, +open: Bool, eb: {Nat.is_eq(m, n) == same : Bool}, +kph: {pc.Kowe.at(same, n, m, f) == True{} : Bool}, +kph0: {pc.Kowe.at(Nat.is_eq(m, n), n, m, f) == True{} : Bool}, +kin: {pc.Old(rest, m) == True{} : Bool}) -> {pc.K(Ch.owe(Maybe.or(&2, Ch.Fate, Ch.fate.here(same, f), Ch.fate(rest, n)), kr, n, open, Ch.Sub{m, f} <> rest)) == True{} : Bool}:
  match same:
    case True{}:
      match f:
        case Ch.Queued{}:
          pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, Ch.Queued{}), pc.Old(rest, m), kph0, kin)
        case Ch.Withdrawn{}:
          pc.and_in(pc.Kowe.at(Nat.is_eq(m, 1n+n), 1n+n, m, Ch.Withdrawn{}), pc.Old(rest, m), pc.kat_w(Nat.is_eq(m, 1n+n), m, n, eb), kin)
        case Ch.Placed{}:
          kin
    case False{}:
      %pc.old_none(rest, m, n, kin, pc.le_pred(m, n, pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)))) : {pc.K(Ch.owe(_, kr, n, open, Ch.Sub{m, f} <> rest)) == True{} : Bool}
      pc.K_new(open, kr, n, m, f, rest, kph, kph0, kin)

# the report rule keeps K
def pc.K_owe(inbox: List<&2, Ch.Sub>, +kr: Ch.Report, +n: Nat, +open: Bool, +kph: {pc.Kowe(inbox, n) == True{} : Bool}, kin: {pc.Kin(inbox) == True{} : Bool}) -> {pc.K(Ch.owe(Ch.fate(inbox, n), kr, n, open, inbox)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.K_new0(open, kr, n, kph)
    case s <> rest:
      match s:
        case Ch.Sub{+m, f}:
          pc.K_owe.at(Nat.is_eq(m, n), kr, n, m, f, rest, open, {==}, kph, kph, kin)

# the abort keeps K: a delete of a watched child owes report 1, which has
# no submission yet
def pc.K_cut(ph: Ch.Ph, del: Bool, +inbox: List<&2, Ch.Sub>, +open: Bool, kph: {pc.Kph(ph, inbox) == True{} : Bool}, kin: {pc.Kin(inbox) == True{} : Bool}) -> {pc.K(Ch.St{Ch.cut.ph(ph, del), None{}, open, inbox}) == True{} : Bool}:
  match ph:
    case Ch.Watching{w}:
      match del:
        case True{}:
          match inbox:
            case Nil{}:
              {==}
            case s <> rest:
              LBoolMisc.child.pc.absurd({pc.K(Ch.St{Ch.Owing{Ch.Cancelled{}, 1n}, None{}, open, s <> rest}) == True{} : Bool}, kph)
        case False{}:
          kin
    case Ch.Owing{kr, +n}:
      pc.and_in(pc.Kowe(inbox, n), pc.Kin(inbox), kph, kin)
    case Ch.Ended{}:
      kin

def pc.K_poll(cut: Maybe<&2, Bool>, ph: Ch.Ph, +inbox: List<&2, Ch.Sub>, +open: Bool, +cfg: Ch.Cfg, +dt: Nat, +o: Ch.Obs, +kph: {pc.Kph(ph, inbox) == True{} : Bool}, +kin: {pc.Kin(inbox) == True{} : Bool}) -> {pc.K(Ch.task(cfg, ph, cut, open, inbox, dt, o)) == True{} : Bool}:
  match cut:
    case None{}:
      match ph:
        case Ch.Watching{+w}:
          match inbox:
            case Nil{}:
              pc.and_in(pc.Kph(Ch.watched(Ch.look(cfg, w, 1n+dt, o)), Nil{}), True{}, pc.Kph_watched(Ch.look(cfg, w, 1n+dt, o)), {==})
            case s <> rest:
              LBoolMisc.child.pc.absurd({pc.K(Ch.task(cfg, Ch.Watching{w}, None{}, open, s <> rest, dt, o)) == True{} : Bool}, kph)
        case Ch.Owing{kr, +n}:
          pc.K_owe(inbox, kr, n, open, kph, kin)
        case Ch.Ended{}:
          kin
    case Some{del}:
      pc.K_cut(ph, del, inbox, open, kph, kin)

# a delivery or withdrawal keeps K: it touches the newest submission only
def pc.K_act(inbox: List<&2, Ch.Sub>, ph: Ch.Ph, +a: Ch.Act, +kph: {pc.Kph(ph, inbox) == True{} : Bool}, +kin: {pc.Kin(inbox) == True{} : Bool}) -> {Bool.and(pc.Kph(ph, Ch.act(inbox, a)), pc.Kin(Ch.act(inbox, a))) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.and_in(pc.Kph(ph, Nil{}), True{}, kph, {==})
    case s <> +rest:
      match s:
        case Ch.Sub{+m, +f}:
          match ph:
            case Ch.Watching{w}:
              LBoolMisc.child.pc.absurd({Bool.and(pc.Kph(Ch.Watching{w}, Ch.act(Ch.Sub{m, f} <> rest, a)), pc.Kin(Ch.act(Ch.Sub{m, f} <> rest, a))) == True{} : Bool}, kph)
            case Ch.Owing{kr, +n}:
              pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, Ch.Fate.act(a, m, f)), pc.Old(Ch.act(rest, a), m), pc.kat_act(Nat.is_eq(m, n), n, m, f, a, kph), pc.old_act(rest, m, a, kin))
            case Ch.Ended{}:
              pc.old_act(rest, m, a, kin)

# every event keeps K
def pc.K_step(+cfg: Ch.Cfg, s: Ch.St, e: Ch.Ev, +k: {pc.K(s) == True{} : Bool}) -> {pc.K(Ch.step(cfg, s, e)) == True{} : Bool}:
  match s:
    case Ch.St{+ph, +cut, +open, +inbox}:
      match e:
        case Ch.Poll{+dt, +o}:
          pc.K_poll(cut, ph, inbox, open, cfg, dt, o, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case Ch.Deliver{+m}:
          pc.K_act(inbox, ph, Ch.Place{m}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case Ch.Withdraw{+m}:
          pc.K_act(inbox, ph, Ch.Pull{m}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case Ch.Abort{}:
          pc.K_act(inbox, ph, Ch.PullAll{}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case Ch.Shut{}:
          pc.K_act(inbox, ph, Ch.PullAll{}, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))
        case Ch.Reopen{}:
          k
        case Ch.Cut{del}:
          k

def pc.K_run(evs: List<&2, Ch.Ev>, +cfg: Ch.Cfg, +s: Ch.St, k: {pc.K(s) == True{} : Bool}) -> {pc.K(Ch.run(evs, cfg, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      k
    case +e <> t:
      pc.K_run(t, cfg, Ch.step(cfg, s, e), pc.K_step(cfg, s, e, k))

def pw6.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

# Child
# -----

def pw6.mnat(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FCh.get_maybe_nat(FCh.put_maybe_nat(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FCh.get_maybe_nat.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == FCh.get_maybe_nat.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FCh.get_maybe_nat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def pw6.w(w: Ch.W, +rest: String, +h: {Child.wire_w_fits(w) == True{} : Bool}) -> {Wr.Got{w, rest} == FCh.get_w(FCh.put_w(w, rest)) : Wr.Dec<Ch.W>}:
  match w:
    case Ch.W{+t, +l, +n}:
      +ln = LBoolAnd.wr_and_r(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)
      %pw6.mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)), LBoolAnd.wr_and_l(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.t(_) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(l, Wr.put_nat(n, rest), LBoolAnd.wr_and_l(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.l(t, _) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(n, rest, LBoolAnd.wr_and_r(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.n(t, l, _) : Wr.Dec<Ch.W>}
      {==}
