# eukhe: lemmas the proofs of area child share

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child/entry.bend as Child
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def pc.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.child.pc.absurd({False{} == True{} : Bool}, e)

def pc.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LLogicLogic.child.pc.absurd({b == True{} : Bool}, e)

def pc.and_in(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LLogicLogic.child.pc.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

def pc.le_of_eq(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.child.pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_of_eq(p, q, e)

def pc.le_pred(+a: Nat, +b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      LNat.child.pc.le_zero(b)
    case 1n+p 0n:
      LLogicLogic.child.pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
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
    case Ch.Read{}:
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
      LLogicLogic.pc.lt_ne({None{} == Some{f} : Maybe<&2, Ch.Fate>}, j, n, lt, eb)
    case False{}:
      ih

def pc.old_none(rest: List<&2, Ch.Sub>, +m: Nat, +n: Nat, +o: {pc.Old(rest, m) == True{} : Bool}, +le: {Nat.is_le(m, n) == True{} : Bool}) -> {None{} == Ch.fate(rest, n) : Maybe<&2, Ch.Fate>}:
  match rest:
    case Nil{}:
      {==}
    case s <> +r:
      match s:
        case Ch.Sub{+j, +f}:
          pc.old_none.at(Nat.is_eq(j, n), j, n, f, r, {==}, LNat.child.pc.le_trans(1n+j, m, n, pc.old_lt(f, j, m, r, o), le), pc.old_none(r, j, n, pc.old_tail(f, j, m, r, o), pc.le_pred(j, n, LNat.child.pc.le_trans(1n+j, m, n, pc.old_lt(f, j, m, r, o), le))))

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
              LLogicLogic.child.pc.absurd({0n == Ch.placed(Ch.Sub{j, Ch.Queued{}} <> r) : Nat}, o)
            case Ch.Withdrawn{}:
              pc.old_placed(r, j, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o))
            case Ch.Placed{}:
              LLogicLogic.child.pc.absurd({0n == Ch.placed(Ch.Sub{j, Ch.Placed{}} <> r) : Nat}, o)
            case Ch.Read{}:
              LLogicLogic.child.pc.absurd({0n == Ch.placed(Ch.Sub{j, Ch.Read{}} <> r) : Nat}, o)

# no submission in an old list is read
def pc.old_reads(rest: List<&2, Ch.Sub>, +m: Nat, o: {pc.Old(rest, m) == True{} : Bool}) -> {0n == Ch.reads(rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case Ch.Sub{+j, f}:
          match f:
            case Ch.Queued{}:
              LLogicLogic.child.pc.absurd({0n == Ch.reads(Ch.Sub{j, Ch.Queued{}} <> r) : Nat}, o)
            case Ch.Withdrawn{}:
              pc.old_reads(r, j, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o))
            case Ch.Placed{}:
              LLogicLogic.child.pc.absurd({0n == Ch.reads(Ch.Sub{j, Ch.Placed{}} <> r) : Nat}, o)
            case Ch.Read{}:
              LLogicLogic.child.pc.absurd({0n == Ch.reads(Ch.Sub{j, Ch.Read{}} <> r) : Nat}, o)

# no submission in an old list is queued
def pc.old_queued(rest: List<&2, Ch.Sub>, +m: Nat, o: {pc.Old(rest, m) == True{} : Bool}) -> {0n == Ch.queued(rest) : Nat}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case Ch.Sub{+j, f}:
          match f:
            case Ch.Queued{}:
              LLogicLogic.child.pc.absurd({0n == Ch.queued(Ch.Sub{j, Ch.Queued{}} <> r) : Nat}, o)
            case Ch.Withdrawn{}:
              pc.old_queued(r, j, pc.and_r(Nat.is_le(1n+j, m), pc.Old(r, j), o))
            case Ch.Placed{}:
              LLogicLogic.child.pc.absurd({0n == Ch.queued(Ch.Sub{j, Ch.Placed{}} <> r) : Nat}, o)
            case Ch.Read{}:
              LLogicLogic.child.pc.absurd({0n == Ch.queued(Ch.Sub{j, Ch.Read{}} <> r) : Nat}, o)

# a delivery or withdrawal leaves a withdrawn submission withdrawn
def pc.isW_act(f: Ch.Fate, +a: Ch.Act, +i: Nat, w: {pc.isW(f) == True{} : Bool}) -> {pc.isW(Ch.Fate.act(a, i, f)) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      LLogicLogic.child.pc.absurd({pc.isW(Ch.Fate.act(a, i, Ch.Queued{})) == True{} : Bool}, w)
    case Ch.Withdrawn{}:
      {==}
    case Ch.Placed{}:
      LLogicLogic.child.pc.absurd({pc.isW(Ch.Fate.act(a, i, Ch.Placed{})) == True{} : Bool}, w)
    case Ch.Read{}:
      LLogicLogic.child.pc.absurd({pc.isW(Ch.Fate.act(a, i, Ch.Read{})) == True{} : Bool}, w)

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
      LLogicLogic.child.pc.absurd({pc.Kowe.at(False{}, n, m, f) == True{} : Bool}, e)

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
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, Ch.Queued{}), True{}, pc.kat(Nat.is_eq(n, n), n, n, Ch.Queued{}, LNat.child.pc.eq_refl(n)), {==})
    case False{}:
      pc.and_in(Nat.is_eq(n, 1n), True{}, kph, {==})

# a submission after the withdrawn one m
def pc.K_new(open: Bool, +kr: Ch.Report, +n: Nat, +m: Nat, +f: Ch.Fate, +rest: List<&2, Ch.Sub>, +kph: {Bool.and(Nat.is_eq(1n+m, n), pc.isW(f)) == True{} : Bool}, kph0: {pc.Kowe.at(Nat.is_eq(m, n), n, m, f) == True{} : Bool}, kin: {pc.Old(rest, m) == True{} : Bool}) -> {pc.K(Ch.owe.new(open, kr, n, Ch.Sub{m, f} <> rest)) == True{} : Bool}:
  match open:
    case True{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, Ch.Queued{}), pc.Old(Ch.Sub{m, f} <> rest, n), pc.kat(Nat.is_eq(n, n), n, n, Ch.Queued{}, LNat.child.pc.eq_refl(n)), pc.and_in(pc.isW(f), Bool.and(Nat.is_le(1n+m, n), pc.Old(rest, m)), pc.and_r(Nat.is_eq(1n+m, n), pc.isW(f), kph), pc.and_in(Nat.is_le(1n+m, n), pc.Old(rest, m), pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)), kin)))
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
        case Ch.Read{}:
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
              LLogicLogic.child.pc.absurd({pc.K(Ch.St{Ch.Owing{Ch.Cancelled{}, 1n}, None{}, open, s <> rest}) == True{} : Bool}, kph)
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
              LLogicLogic.child.pc.absurd({pc.K(Ch.task(cfg, Ch.Watching{w}, None{}, open, s <> rest, dt, o)) == True{} : Bool}, kph)
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
              LLogicLogic.child.pc.absurd({Bool.and(pc.Kph(Ch.Watching{w}, Ch.act(Ch.Sub{m, f} <> rest, a)), pc.Kin(Ch.act(Ch.Sub{m, f} <> rest, a))) == True{} : Bool}, kph)
            case Ch.Owing{kr, +n}:
              pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, Ch.Fate.act(a, m, f)), pc.Old(Ch.act(rest, a), m), pc.kat_act(Nat.is_eq(m, n), n, m, f, a, kph), pc.old_act(rest, m, a, kin))
            case Ch.Ended{}:
              pc.old_act(rest, m, a, kin)

# the parent's read of the owed report n keeps K: it reads the newest
# submission n, or stands a read n before the withdrawn n - 1
def pc.K_read.at(same: Bool, +n: Nat, +m: Nat, +f: Ch.Fate, +rest: List<&2, Ch.Sub>, eb: {Nat.is_eq(m, n) == same : Bool}, +kph: {pc.Kowe.at(same, n, m, f) == True{} : Bool}, +kin: {pc.Old(rest, m) == True{} : Bool}) -> {Bool.and(pc.Kowe(Ch.read.at(same, n, Ch.Sub{m, f}, rest), n), pc.Kin(Ch.read.at(same, n, Ch.Sub{m, f}, rest))) == True{} : Bool}:
  match same:
    case True{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(m, n), n, m, Ch.Fate.read(f)), pc.Old(rest, m), pc.kat(Nat.is_eq(m, n), n, m, Ch.Fate.read(f), eb), kin)
    case False{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, Ch.Read{}), pc.Old(Ch.Sub{m, f} <> rest, n), pc.kat(Nat.is_eq(n, n), n, n, Ch.Read{}, LNat.child.pc.eq_refl(n)), pc.and_in(pc.isW(f), Bool.and(Nat.is_le(1n+m, n), pc.Old(rest, m)), pc.and_r(Nat.is_eq(1n+m, n), pc.isW(f), kph), pc.and_in(Nat.is_le(1n+m, n), pc.Old(rest, m), pc.le_of_eq(1n+m, n, pc.and_l(Nat.is_eq(1n+m, n), pc.isW(f), kph)), kin)))

def pc.K_read.sub(inbox: List<&2, Ch.Sub>, +n: Nat, kph: {pc.Kowe(inbox, n) == True{} : Bool}, kin: {pc.Kin(inbox) == True{} : Bool}) -> {Bool.and(pc.Kowe(Ch.read.sub(inbox, n), n), pc.Kin(Ch.read.sub(inbox, n))) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.and_in(pc.Kowe.at(Nat.is_eq(n, n), n, n, Ch.Read{}), True{}, pc.kat(Nat.is_eq(n, n), n, n, Ch.Read{}, LNat.child.pc.eq_refl(n)), {==})
    case s <> rest:
      match s:
        case Ch.Sub{+m, f}:
          pc.K_read.at(Nat.is_eq(m, n), n, m, f, rest, {==}, kph, kin)

def pc.K_read(ph: Ch.Ph, +inbox: List<&2, Ch.Sub>, kph: {pc.Kph(ph, inbox) == True{} : Bool}, kin: {pc.Kin(inbox) == True{} : Bool}) -> {Bool.and(pc.Kph(ph, Ch.read(ph, inbox)), pc.Kin(Ch.read(ph, inbox))) == True{} : Bool}:
  match ph:
    case Ch.Watching{w}:
      pc.and_in(pc.Kph(Ch.Watching{w}, inbox), pc.Kin(inbox), kph, kin)
    case Ch.Owing{kr, +n}:
      pc.K_read.sub(inbox, n, kph, kin)
    case Ch.Ended{}:
      kin

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
        case Ch.Collect{}:
          pc.K_read(ph, inbox, pc.and_l(pc.Kph(ph, inbox), pc.Kin(inbox), k), pc.and_r(pc.Kph(ph, inbox), pc.Kin(inbox), k))

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
      +ln = LLogicBool.wr_and_r(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)
      %pw6.mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)), LLogicBool.wr_and_l(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.t(_) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(l, Wr.put_nat(n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.l(t, _) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(n, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.n(t, l, _) : Wr.Dec<Ch.W>}
      {==}

# The entry's spelled wire
# ------------------------
# The spec spellers of laws/child/entry.bend (Child.ch_spell_*): the code's reply
# encoders spell as they do (sp.*), each decoder reads a spelled value back
# (rt.*), and a spelled request runs to its last stage (lo.run), which
# answers the spelled model decision (lo.answer) or, with input left, the
# error form (lo.left, lo.left_ok).

def sp.mnat(m: Maybe<&2, Nat>, rest: String) -> {FCh.put_maybe_nat(m, rest) == Child.ch_spell_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def sp.w(w: Ch.W, rest: String) -> {FCh.put_w(w, rest) == Child.ch_spell_w(w, rest) : String}:
  match w:
    case Ch.W{t, l, n}:
      sp.mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)))

def sp.report(k: Ch.Report, rest: String) -> {FCh.put_report(k, rest) == Child.ch_spell_report(k, rest) : String}:
  match k:
    case Ch.Completed{}:
      {==}
    case Ch.Failed{}:
      {==}
    case Ch.Cancelled{}:
      {==}
    case Ch.Stalled{}:
      {==}
    case Ch.Unreachable{}:
      {==}

def sp.call(c: Ch.Call, +rest: String) -> {FCh.put_call(c, rest) == Child.ch_spell_call(c, rest) : String}:
  match c:
    case Ch.Watches{+w}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FCh.put_w(w, rest), Child.ch_spell_w(w, rest), sp.w(w, rest))
    case Ch.Reports{+k}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FCh.put_report(k, rest), Child.ch_spell_report(k, rest), sp.report(k, rest))
    case Ch.Settles{why}:
      match why:
        case None{}:
          {==}
        case Some{+k}:
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(1n, z)), FCh.put_report(k, rest), Child.ch_spell_report(k, rest), sp.report(k, rest))

def sp.move(m: Ch.Move, rest: String) -> {FCh.put_move(m, rest) == Child.ch_spell_move(m, rest) : String}:
  match m:
    case Ch.Submit{n}:
      {==}
    case Ch.Await{}:
      {==}
    case Ch.Resubmit{n}:
      {==}
    case Ch.Delivered{}:
      {==}

def sp.ph(p: Ch.Ph, +rest: String) -> {FCh.put_ph(p, rest) == Child.ch_spell_ph(p, rest) : String}:
  match p:
    case Ch.Watching{+w}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FCh.put_w(w, rest), Child.ch_spell_w(w, rest), sp.w(w, rest))
    case Ch.Owing{+k, +n}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FCh.put_report(k, Wr.put_nat(n, rest)), Child.ch_spell_report(k, Wr.put_nat(n, rest)), sp.report(k, Wr.put_nat(n, rest)))
    case Ch.Ended{}:
      {==}

def rt.mnat(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FCh.get_maybe_nat(Child.ch_spell_mnat(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FCh.get_maybe_nat.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == FCh.get_maybe_nat.go(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FCh.get_maybe_nat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def rt.w(w: Ch.W, +rest: String, +h: {Child.wire_w_fits(w) == True{} : Bool}) -> {Wr.Got{w, rest} == FCh.get_w(Child.ch_spell_w(w, rest)) : Wr.Dec<Ch.W>}:
  match w:
    case Ch.W{+t, +l, +n}:
      +ln = LLogicBool.wr_and_r(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)
      %rt.mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)), LLogicBool.wr_and_l(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.t(_) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(l, Wr.put_nat(n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.l(t, _) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(n, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == FCh.get_w.n(t, l, _) : Wr.Dec<Ch.W>}
      {==}

def rt.cfg(c: Ch.Cfg, +rest: String, +h: {Child.wire_cfg_fits(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FCh.get_cfg(Child.ch_spell_cfg(c, rest)) : Wr.Dec<Ch.Cfg>}:
  match c:
    case Ch.Cfg{+s, +f}:
      %LWire.pw6.nat(s, Wr.put_nat(f, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(f), h)) : {Wr.Got{Ch.Cfg{s, f}, rest} == FCh.get_cfg.s(_) : Wr.Dec<Ch.Cfg>}
      %LWire.pw6.nat(f, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(f), h)) : {Wr.Got{Ch.Cfg{s, f}, rest} == FCh.get_cfg.f(s, _) : Wr.Dec<Ch.Cfg>}
      {==}

def rt.obs(o: Ch.Obs, +rest: String, +h: {Child.wire_obs_fits(o) == True{} : Bool}) -> {Wr.Got{o, rest} == FCh.get_obs(Child.ch_spell_obs(o, rest)) : Wr.Dec<Ch.Obs>}:
  match o:
    case Ch.Busy{+t}:
      %LWire.pw6.nat(0n, Child.ch_spell_mnat(t, rest), {==}) : {Wr.Got{Ch.Busy{t}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      %rt.mnat(t, rest, h) : {Wr.Got{Ch.Busy{t}, rest} == FCh.get_obs.busy(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Lost{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Lost{}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Answered{+r}:
      %LWire.pw6.nat(2n, Wr.put_bool(r, rest), {==}) : {Wr.Got{Ch.Answered{r}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      %pw6.bool(r, rest) : {Wr.Got{Ch.Answered{r}, rest} == FCh.get_obs.answered(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Broke{}:
      %LWire.pw6.nat(3n, rest, {==}) : {Wr.Got{Ch.Broke{}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Gone{}:
      %LWire.pw6.nat(4n, rest, {==}) : {Wr.Got{Ch.Gone{}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      {==}

def rt.mode(m: Ch.Mode, +rest: String) -> {Wr.Got{m, rest} == FCh.get_mode(Child.ch_spell_mode(m, rest)) : Wr.Dec<Ch.Mode>}:
  match m:
    case Ch.Inbox{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Inbox{}, rest} == FCh.get_mode.go(_) : Wr.Dec<Ch.Mode>}
      {==}
    case Ch.Silent{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Silent{}, rest} == FCh.get_mode.go(_) : Wr.Dec<Ch.Mode>}
      {==}

def rt.report(k: Ch.Report, +rest: String) -> {Wr.Got{k, rest} == FCh.get_report(Child.ch_spell_report(k, rest)) : Wr.Dec<Ch.Report>}:
  match k:
    case Ch.Completed{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Completed{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Failed{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Failed{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Cancelled{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Cancelled{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Stalled{}:
      %LWire.pw6.nat(3n, rest, {==}) : {Wr.Got{Ch.Stalled{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Unreachable{}:
      %LWire.pw6.nat(4n, rest, {==}) : {Wr.Got{Ch.Unreachable{}, rest} == FCh.get_report.go(_) : Wr.Dec<Ch.Report>}
      {==}

def rt.fate(f: Ch.Fate, +rest: String) -> {Wr.Got{f, rest} == FCh.get_fate(Child.ch_spell_fate(f, rest)) : Wr.Dec<Ch.Fate>}:
  match f:
    case Ch.Queued{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Queued{}, rest} == FCh.get_fate.go(_) : Wr.Dec<Ch.Fate>}
      {==}
    case Ch.Withdrawn{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Withdrawn{}, rest} == FCh.get_fate.go(_) : Wr.Dec<Ch.Fate>}
      {==}
    case Ch.Placed{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Placed{}, rest} == FCh.get_fate.go(_) : Wr.Dec<Ch.Fate>}
      {==}
    case Ch.Read{}:
      %LWire.pw6.nat(3n, rest, {==}) : {Wr.Got{Ch.Read{}, rest} == FCh.get_fate.go(_) : Wr.Dec<Ch.Fate>}
      {==}

def rt.mfate(f: Maybe<&2, Ch.Fate>, +rest: String) -> {Wr.Got{f, rest} == FCh.get_mfate(Child.ch_spell_mfate(f, rest)) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match f:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FCh.get_mfate.go(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Child.ch_spell_fate(x, rest), {==}) : {Wr.Got{Some{x}, rest} == FCh.get_mfate.go(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      %rt.fate(x, rest) : {Wr.Got{Some{x}, rest} == FCh.get_mfate.some(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      {==}

def rt.ph(p: Ch.Ph, +rest: String, +h: {Child.wire_ph_fits(p) == True{} : Bool}) -> {Wr.Got{p, rest} == FCh.get_ph(Child.ch_spell_ph(p, rest)) : Wr.Dec<Ch.Ph>}:
  match p:
    case Ch.Watching{+w}:
      %LWire.pw6.nat(0n, Child.ch_spell_w(w, rest), {==}) : {Wr.Got{Ch.Watching{w}, rest} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      %rt.w(w, rest, h) : {Wr.Got{Ch.Watching{w}, rest} == FCh.get_ph.watching(_) : Wr.Dec<Ch.Ph>}
      {==}
    case Ch.Owing{+k, +n}:
      %LWire.pw6.nat(1n, Child.ch_spell_report(k, Wr.put_nat(n, rest)), {==}) : {Wr.Got{Ch.Owing{k, n}, rest} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      %rt.report(k, Wr.put_nat(n, rest)) : {Wr.Got{Ch.Owing{k, n}, rest} == FCh.get_ph.owing(_) : Wr.Dec<Ch.Ph>}
      %LWire.pw6.nat(n, rest, h) : {Wr.Got{Ch.Owing{k, n}, rest} == FCh.get_ph.n(k, _) : Wr.Dec<Ch.Ph>}
      {==}
    case Ch.Ended{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Ended{}, rest} == FCh.get_ph.go(_) : Wr.Dec<Ch.Ph>}
      {==}

# the last stage of request r: its answer when nothing is left (left)
def lo.fin(r: FCh.Req, left: Bool) -> String:
  match r:
    case FCh.AskVerdict{c, w, e, o, m}:
      FCh.verdict.fin(left, c, w, e, o, m)
    case FCh.AskMove{f, n}:
      FCh.move.fin(left, f, n)
    case FCh.AskAbort{p, d}:
      FCh.abort.fin(left, p, d)

# a spelled request that fits, then rest, runs to its last stage
def lo.run(r: FCh.Req, +rest: String, +fits: {Child.ch_req_fits(r) == True{} : Bool}) -> {FCh.ffi(Child.ch_spell_req(r, rest)) == lo.fin(r, Wr.end(rest)) : String}:
  match r:
    case FCh.AskVerdict{+c, +w, +e, +o, +m}:
      +h1 = LLogicBool.wr_and_r(Child.wire_cfg_fits(c), Bool.and(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o))), fits)
      +h2 = LLogicBool.wr_and_r(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o)), h1)
      +R = FCh.verdict.fin(Wr.end(rest), c, w, e, o, m)
      %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, Child.ch_spell_mode(m, rest))))), {==}) : {FCh.run(_) == R : String}
      %rt.cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, Child.ch_spell_mode(m, rest)))), LLogicBool.wr_and_l(Child.wire_cfg_fits(c), Bool.and(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o))), fits)) : {FCh.verdict.c(_) == R : String}
      %rt.w(w, Wr.put_nat(e, Child.ch_spell_obs(o, Child.ch_spell_mode(m, rest))), LLogicBool.wr_and_l(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o)), h1)) : {FCh.verdict.w(c, _) == R : String}
      %LWire.pw6.nat(e, Child.ch_spell_obs(o, Child.ch_spell_mode(m, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(e), Child.wire_obs_fits(o), h2)) : {FCh.verdict.e(c, w, _) == R : String}
      %rt.obs(o, Child.ch_spell_mode(m, rest), LLogicBool.wr_and_r(LawsBase.wire_fits(e), Child.wire_obs_fits(o), h2)) : {FCh.verdict.o(c, w, e, _) == R : String}
      %rt.mode(m, rest) : {FCh.verdict.m(c, w, e, o, _) == R : String}
      {==}
    case FCh.AskMove{+f, +n}:
      +R = FCh.move.fin(Wr.end(rest), f, n)
      %LWire.pw6.nat(1n, Child.ch_spell_mfate(f, Wr.put_nat(n, rest)), {==}) : {FCh.run(_) == R : String}
      %rt.mfate(f, Wr.put_nat(n, rest)) : {FCh.move.f(_) == R : String}
      %LWire.pw6.nat(n, rest, fits) : {FCh.move.n(f, _) == R : String}
      {==}
    case FCh.AskAbort{+p, +d}:
      +R = FCh.abort.fin(Wr.end(rest), p, d)
      %LWire.pw6.nat(2n, Child.ch_spell_ph(p, Wr.put_bool(d, rest)), {==}) : {FCh.run(_) == R : String}
      %rt.ph(p, Wr.put_bool(d, rest), fits) : {FCh.abort.ph(_) == R : String}
      %pw6.bool(d, rest) : {FCh.abort.d(p, _) == R : String}
      {==}

# nothing left: the spelled model decision
def lo.answer(r: FCh.Req) -> {lo.fin(r, True{}) == Child.ch_spell_answer(r) : String}:
  match r:
    case FCh.AskVerdict{+c, +w, +e, o, m}:
      sp.call(Ch.verdict(c, w, e, o, m), "")
    case FCh.AskMove{f, +n}:
      sp.move(Ch.owe.next(f, n), "")
    case FCh.AskAbort{p, d}:
      sp.ph(Ch.cut.ph(p, d), "")

# input left: the error form
def lo.left(r: FCh.Req) -> {lo.fin(r, False{}) == Wr.err("child: input left over") : String}:
  match r:
    case FCh.AskVerdict{c, w, e, o, m}:
      {==}
    case FCh.AskMove{f, n}:
      {==}
    case FCh.AskAbort{p, d}:
      {==}

# input left answers the error form, which opens with 'E'
def lo.left_ok(r: FCh.Req, ok: {LawsBase.wire_opens_err(lo.fin(r, False{})) == False{} : Bool}) -> {True{} == False{} : Bool}:
  match r:
    case FCh.AskVerdict{c, w, e, o, m}:
      ok
    case FCh.AskMove{f, n}:
      ok
    case FCh.AskAbort{p, d}:
      ok
