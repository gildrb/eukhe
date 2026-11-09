# eukhe: the proof of LAW child_delivered_once

import Base
import ../../bend/child.bend as Ch
import ../../spec/child.bend as ChS
import ../../laws/child.bend as Child
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

# The report
# ----------

# a clash of constructors proves anything
def child.pc.MD(x: Maybe<&2, Ch.Fate>, t: Type, u: Type) -> Type:
  match x:
    case None{}:
      t
    case Some{f}:
      u

def pc.none_some(-A: Type, -f: Ch.Fate, e: {None{} == Some{f} : Maybe<&2, Ch.Fate>}) -> A:
  %e : child.pc.MD(_, Unit, A)
  Unit{}

def child.pc.ND(n: Nat, t: Type, u: Type) -> Type:
  match n:
    case 0n:
      t
    case 1n+p:
      u

def pc.zero_succ(-A: Type, -p: Nat, e: {0n == 1n+p : Nat}) -> A:
  %e : child.pc.ND(_, Unit, A)
  Unit{}

# x is 0 and 1 at once
def pc.one_zero(-A: Type, x: Nat, e: {0n == x : Nat}, r: {Nat.is_eq(x, 1n) == True{} : Bool}) -> A:
  match x:
    case 0n:
      LLogicLogic.child.pc.absurd(A, r)
    case 1n+p:
      pc.zero_succ(A, p, e)

def pc.eq_next(+m: Nat, +n: Nat, e: {Nat.is_eq(m, n) == True{} : Bool}) -> {Nat.is_eq(m, 1n+n) == False{} : Bool}:
  match m n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.child.pc.absurd({Nat.is_eq(0n, 2n+q) == False{} : Bool}, e)
    case 1n+p 0n:
      LLogicLogic.child.pc.absurd({Nat.is_eq(1n+p, 1n) == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.eq_next(p, q, e)

# delivered_once: `soon` holds when the open, unmarked task owes id n with
# no submission of n yet or n queued, or the report is placed; `ready`
# when n is queued, or the report is placed
def pc.unmarked(cut: Maybe<&2, Bool>) -> Bool:
  match cut:
    case None{}:
      True{}
    case Some{d}:
      False{}

def pc.fq(x: Maybe<&2, Ch.Fate>) -> Bool:
  match x:
    case None{}:
      False{}
    case Some{f}:
      match f:
        case Ch.Queued{}:
          True{}
        case Ch.Withdrawn{}:
          False{}
        case Ch.Placed{}:
          False{}

def pc.fs(x: Maybe<&2, Ch.Fate>) -> Bool:
  match x:
    case None{}:
      True{}
    case Some{f}:
      match f:
        case Ch.Queued{}:
          True{}
        case Ch.Withdrawn{}:
          False{}
        case Ch.Placed{}:
          False{}

def pc.ready(s: ChS.St) -> Bool:
  match s:
    case ChS.St{ph, cut, open, +inbox}:
      match ph:
        case Ch.Watching{w}:
          False{}
        case Ch.Owing{k, +n}:
          Bool.and(pc.unmarked(cut), Bool.and(open, pc.fq(ChS.fate(inbox, n))))
        case Ch.Ended{}:
          Nat.is_eq(ChS.placed(inbox), 1n)

def pc.soon(s: ChS.St) -> Bool:
  match s:
    case ChS.St{ph, cut, open, +inbox}:
      match ph:
        case Ch.Watching{w}:
          False{}
        case Ch.Owing{k, +n}:
          Bool.and(pc.unmarked(cut), Bool.and(open, pc.fs(ChS.fate(inbox, n))))
        case Ch.Ended{}:
          Nat.is_eq(ChS.placed(inbox), 1n)

# the submission just made is found queued
def pc.fs_new(same: Bool, -x: Maybe<&2, Ch.Fate>, e: {same == True{} : Bool}) -> {pc.fs(Maybe.or(&2, Ch.Fate, ChS.fate.here(same, Ch.Queued{}), x)) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.child.pc.absurd({pc.fs(Maybe.or(&2, Ch.Fate, ChS.fate.here(False{}, Ch.Queued{}), x)) == True{} : Bool}, e)

def pc.fq_new(same: Bool, -x: Maybe<&2, Ch.Fate>, e: {same == True{} : Bool}) -> {pc.fq(Maybe.or(&2, Ch.Fate, ChS.fate.here(same, Ch.Queued{}), x)) == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.child.pc.absurd({pc.fq(Maybe.or(&2, Ch.Fate, ChS.fate.here(False{}, Ch.Queued{}), x)) == True{} : Bool}, e)

def pc.fs_off(same: Bool, -f: Ch.Fate, e: {same == False{} : Bool}) -> {pc.fs(Maybe.or(&2, Ch.Fate, ChS.fate.here(same, f), None{})) == True{} : Bool}:
  match same:
    case True{}:
      LLogicLogic.child.pc.absurd({pc.fs(Maybe.or(&2, Ch.Fate, ChS.fate.here(True{}, f), None{})) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      {==}

def pc.fs_of_fq(x: Maybe<&2, Ch.Fate>, e: {pc.fq(x) == True{} : Bool}) -> {pc.fs(x) == True{} : Bool}:
  match x:
    case None{}:
      LLogicLogic.child.pc.absurd({pc.fs(None{}) == True{} : Bool}, e)
    case Some{f}:
      match f:
        case Ch.Queued{}:
          {==}
        case Ch.Withdrawn{}:
          LLogicLogic.child.pc.absurd({pc.fs(Some{Ch.Withdrawn{}}) == True{} : Bool}, e)
        case Ch.Placed{}:
          LLogicLogic.child.pc.absurd({pc.fs(Some{Ch.Placed{}}) == True{} : Bool}, e)

# no queued submission where none exists
def pc.fq_none(-A: Type, x: Maybe<&2, Ch.Fate>, e: {None{} == x : Maybe<&2, Ch.Fate>}, r: {pc.fq(x) == True{} : Bool}) -> A:
  match x:
    case None{}:
      LLogicLogic.child.pc.absurd(A, r)
    case Some{f}:
      pc.none_some(A, f, e)

# one step of the report rule from K leaves the report soon
def pc.soon_owe.at(same: Bool, +kr: Ch.Report, +n: Nat, +m: Nat, f: Ch.Fate, +rest: List<&2, ChS.Sub>, +eb: {Nat.is_eq(m, n) == same : Bool}, kph: {LA.pc.Kowe.at(same, n, m, f) == True{} : Bool}, +kin: {LA.pc.Old(rest, m) == True{} : Bool}) -> {pc.soon(ChS.owe.do(Ch.owe.next(Maybe.or(&2, Ch.Fate, ChS.fate.here(same, f), ChS.fate(rest, n)), n), kr, n, True{}, ChS.Sub{m, f} <> rest)) == True{} : Bool}:
  match same:
    case True{}:
      match f:
        case Ch.Queued{}:
          pc.fs_new(Nat.is_eq(m, n), ChS.fate(rest, n), eb)
        case Ch.Withdrawn{}:
          %LA.pc.old_none(rest, m, 1n+n, kin, LNat.pc.le_succ(m, n, LA.pc.le_of_eq(m, n, eb))) : {pc.fs(Maybe.or(&2, Ch.Fate, ChS.fate.here(Nat.is_eq(m, 1n+n), Ch.Withdrawn{}), _)) == True{} : Bool}
          pc.fs_off(Nat.is_eq(m, 1n+n), Ch.Withdrawn{}, pc.eq_next(m, n, eb))
        case Ch.Placed{}:
          %LA.pc.old_placed(rest, m, kin) : {Nat.is_eq(Nat.add(1n, _), 1n) == True{} : Bool}
          {==}
    case False{}:
      %LA.pc.old_none(rest, m, n, kin, LA.pc.le_pred(m, n, LA.pc.le_of_eq(1n+m, n, LA.pc.and_l(Nat.is_eq(1n+m, n), LA.pc.isW(f), kph)))) : {pc.soon(ChS.owe.do(Ch.owe.next(_, n), kr, n, True{}, ChS.Sub{m, f} <> rest)) == True{} : Bool}
      pc.fs_new(Nat.is_eq(n, n), ChS.fate(ChS.Sub{m, f} <> rest, n), LNat.child.pc.eq_refl(n))

def pc.soon_owe(inbox: List<&2, ChS.Sub>, +kr: Ch.Report, +n: Nat, kph: {LA.pc.Kowe(inbox, n) == True{} : Bool}, kin: {LA.pc.Kin(inbox) == True{} : Bool}) -> {pc.soon(ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      pc.fs_new(Nat.is_eq(n, n), None{}, LNat.child.pc.eq_refl(n))
    case s <> rest:
      match s:
        case ChS.Sub{+m, f}:
          pc.soon_owe.at(Nat.is_eq(m, n), kr, n, m, f, rest, {==}, kph, kin)

# a soon report is ready after one more task step
def pc.ready_owe(x: Maybe<&2, Ch.Fate>, +kr: Ch.Report, +n: Nat, +inbox: List<&2, ChS.Sub>, ex: {ChS.fate(inbox, n) == x : Maybe<&2, Ch.Fate>}, sn: {pc.fs(x) == True{} : Bool}) -> {pc.ready(ChS.owe.do(Ch.owe.next(x, n), kr, n, True{}, inbox)) == True{} : Bool}:
  match x:
    case None{}:
      pc.fq_new(Nat.is_eq(n, n), ChS.fate(inbox, n), LNat.child.pc.eq_refl(n))
    case Some{y}:
      match y:
        case Ch.Queued{}:
          %Equal.sym(Maybe<&2, Ch.Fate>, ChS.fate(inbox, n), Some{Ch.Queued{}}, ex) : {pc.fq(_) == True{} : Bool}
          {==}
        case Ch.Withdrawn{}:
          LLogicLogic.child.pc.absurd({pc.ready(ChS.owe.do(Ch.owe.next(Some{Ch.Withdrawn{}}, n), kr, n, True{}, inbox)) == True{} : Bool}, sn)
        case Ch.Placed{}:
          LLogicLogic.child.pc.absurd({pc.ready(ChS.owe.do(Ch.owe.next(Some{Ch.Placed{}}, n), kr, n, True{}, inbox)) == True{} : Bool}, sn)

def pc.ready_soon(+cfg: Ch.Cfg, s: ChS.St, +d: Nat, +o: Ch.Obs, sn: {pc.soon(s) == True{} : Bool}) -> {pc.ready(ChS.step(cfg, s, ChS.Poll{d, o})) == True{} : Bool}:
  match s:
    case ChS.St{ph, cut, open, +inbox}:
      match ph:
        case Ch.Watching{w}:
          LLogicLogic.child.pc.absurd({pc.ready(ChS.step(cfg, ChS.St{Ch.Watching{w}, cut, open, inbox}, ChS.Poll{d, o})) == True{} : Bool}, sn)
        case Ch.Owing{kr, +n}:
          match cut:
            case None{}:
              match open:
                case True{}:
                  pc.ready_owe(ChS.fate(inbox, n), kr, n, inbox, {==}, sn)
                case False{}:
                  LLogicLogic.child.pc.absurd({pc.ready(ChS.step(cfg, ChS.St{Ch.Owing{kr, n}, None{}, False{}, inbox}, ChS.Poll{d, o})) == True{} : Bool}, sn)
            case Some{del}:
              LLogicLogic.child.pc.absurd({pc.ready(ChS.step(cfg, ChS.St{Ch.Owing{kr, n}, Some{del}, open, inbox}, ChS.Poll{d, o})) == True{} : Bool}, sn)
        case Ch.Ended{}:
          match cut:
            case None{}:
              sn
            case Some{del}:
              sn

def pc.soon_of_ready(s: ChS.St, r: {pc.ready(s) == True{} : Bool}) -> {pc.soon(s) == True{} : Bool}:
  match s:
    case ChS.St{ph, cut, open, +inbox}:
      match ph:
        case Ch.Watching{w}:
          r
        case Ch.Owing{k, +n}:
          match cut:
            case None{}:
              match open:
                case True{}:
                  pc.fs_of_fq(ChS.fate(inbox, n), r)
                case False{}:
                  r
            case Some{d}:
              r
        case Ch.Ended{}:
          r

# a delivery of the queued submission n places it: one entry placed
def pc.del_at(same: Bool, +n: Nat, +m: Nat, f: Ch.Fate, +rest: List<&2, ChS.Sub>, eb: {Nat.is_eq(m, n) == same : Bool}, kph: {LA.pc.Kowe.at(same, n, m, f) == True{} : Bool}, +kin: {LA.pc.Old(rest, m) == True{} : Bool}, r: {pc.fq(Maybe.or(&2, Ch.Fate, ChS.fate.here(same, f), ChS.fate(rest, n))) == True{} : Bool}) -> {ChS.placed(ChS.act(ChS.Sub{m, f} <> rest, ChS.Place{n})) == 1n : Nat}:
  match same:
    case True{}:
      match f:
        case Ch.Queued{}:
          %LA.pc.old_placed(ChS.act(rest, ChS.Place{n}), m, LA.pc.old_act(rest, m, ChS.Place{n}, kin)) : {Nat.add(ChS.Fate.placed(ChS.Act.hit(Nat.is_eq(m, n), Ch.Placed{})), _) == 1n : Nat}
          %Equal.sym(Bool, Nat.is_eq(m, n), True{}, eb) : {Nat.add(ChS.Fate.placed(ChS.Act.hit(_, Ch.Placed{})), 0n) == 1n : Nat}
          {==}
        case Ch.Withdrawn{}:
          LLogicLogic.child.pc.absurd({ChS.placed(ChS.act(ChS.Sub{m, Ch.Withdrawn{}} <> rest, ChS.Place{n})) == 1n : Nat}, r)
        case Ch.Placed{}:
          LLogicLogic.child.pc.absurd({ChS.placed(ChS.act(ChS.Sub{m, Ch.Placed{}} <> rest, ChS.Place{n})) == 1n : Nat}, r)
    case False{}:
      pc.fq_none({ChS.placed(ChS.act(ChS.Sub{m, f} <> rest, ChS.Place{n})) == 1n : Nat}, ChS.fate(rest, n), LA.pc.old_none(rest, m, n, kin, LA.pc.le_pred(m, n, LA.pc.le_of_eq(1n+m, n, LA.pc.and_l(Nat.is_eq(1n+m, n), LA.pc.isW(f), kph)))), r)

# a delivery of any id leaves a placed report placed once
def pc.del_end(inbox: List<&2, ChS.Sub>, +x: Nat, kin: {LA.pc.Kin(inbox) == True{} : Bool}, r: {Nat.is_eq(ChS.placed(inbox), 1n) == True{} : Bool}) -> {ChS.placed(ChS.act(inbox, ChS.Place{x})) == 1n : Nat}:
  match inbox:
    case Nil{}:
      LLogicLogic.child.pc.absurd({ChS.placed(ChS.act(Nil{}, ChS.Place{x})) == 1n : Nat}, r)
    case s <> +rest:
      match s:
        case ChS.Sub{+m, f}:
          match f:
            case Ch.Queued{}:
              pc.one_zero({ChS.placed(ChS.act(ChS.Sub{m, Ch.Queued{}} <> rest, ChS.Place{x})) == 1n : Nat}, ChS.placed(rest), LA.pc.old_placed(rest, m, kin), r)
            case Ch.Withdrawn{}:
              pc.one_zero({ChS.placed(ChS.act(ChS.Sub{m, Ch.Withdrawn{}} <> rest, ChS.Place{x})) == 1n : Nat}, ChS.placed(rest), LA.pc.old_placed(rest, m, kin), r)
            case Ch.Placed{}:
              %LA.pc.old_placed(ChS.act(rest, ChS.Place{x}), m, LA.pc.old_act(rest, m, ChS.Place{x}, kin)) : {Nat.add(1n, _) == 1n : Nat}
              {==}

def pc.ready_deliver0(+cfg: Ch.Cfg, s: ChS.St, +k: {LA.pc.K(s) == True{} : Bool}, r: {pc.ready(s) == True{} : Bool}) -> {ChS.St.placed(ChS.step(cfg, s, ChS.Deliver{ChS.St.owed(s)})) == 1n : Nat}:
  match s:
    case ChS.St{ph, cut, open, +inbox}:
      match ph:
        case Ch.Watching{w}:
          LLogicLogic.child.pc.absurd({ChS.St.placed(ChS.step(cfg, ChS.St{Ch.Watching{w}, cut, open, inbox}, ChS.Deliver{0n})) == 1n : Nat}, r)
        case Ch.Owing{kr, +n}:
          match cut:
            case None{}:
              match open:
                case True{}:
                  match inbox:
                    case Nil{}:
                      LLogicLogic.child.pc.absurd({ChS.St.placed(ChS.step(cfg, ChS.St{Ch.Owing{kr, n}, None{}, True{}, Nil{}}, ChS.Deliver{n})) == 1n : Nat}, r)
                    case s2 <> +rest:
                      match s2:
                        case ChS.Sub{+m, +f}:
                          pc.del_at(Nat.is_eq(m, n), n, m, f, rest, {==}, LA.pc.and_l(LA.pc.Kowe.at(Nat.is_eq(m, n), n, m, f), LA.pc.Old(rest, m), k), LA.pc.and_r(LA.pc.Kowe.at(Nat.is_eq(m, n), n, m, f), LA.pc.Old(rest, m), k), r)
                case False{}:
                  LLogicLogic.child.pc.absurd({ChS.St.placed(ChS.step(cfg, ChS.St{Ch.Owing{kr, n}, None{}, False{}, inbox}, ChS.Deliver{n})) == 1n : Nat}, r)
            case Some{del}:
              LLogicLogic.child.pc.absurd({ChS.St.placed(ChS.step(cfg, ChS.St{Ch.Owing{kr, n}, Some{del}, open, inbox}, ChS.Deliver{n})) == 1n : Nat}, r)
        case Ch.Ended{}:
          pc.del_end(inbox, 0n, k, r)

def pc.ready_deliver(+cfg: Ch.Cfg, +s: ChS.St, +m: Nat, k: {LA.pc.K(s) == True{} : Bool}, r: {pc.ready(s) == True{} : Bool}, em: {ChS.St.owed(s) == m : Nat}) -> {ChS.St.placed(ChS.step(cfg, s, ChS.Deliver{m})) == 1n : Nat}:
  %em : {ChS.St.placed(ChS.step(cfg, s, ChS.Deliver{_})) == 1n : Nat}
  pc.ready_deliver0(cfg, s, k, r)

# from any state that owes the report: a reopen, three task steps (the
# first may run a pending abort, which hands the report on), and a
# delivery of the id the task then owes place it, exactly once
def pc.delivered(+cfg: Ch.Cfg, s: ChS.St, +d1: Nat, +o1: Ch.Obs, +d2: Nat, +o2: Ch.Obs, +d3: Nat, +o3: Ch.Obs, +m: Nat, +k: {LA.pc.K(s) == True{} : Bool}, ow: {ChS.owing(ChS.St.ph(s)) == True{} : Bool}, em: {ChS.St.owed(ChS.run([ChS.Reopen{}, ChS.Poll{d1, o1}, ChS.Poll{d2, o2}, ChS.Poll{d3, o3}], cfg, s)) == m : Nat}) -> {ChS.St.placed(ChS.run([ChS.Reopen{}, ChS.Poll{d1, o1}, ChS.Poll{d2, o2}, ChS.Poll{d3, o3}, ChS.Deliver{m}], cfg, s)) == 1n : Nat}:
  match s:
    case ChS.St{ph, cut, open, +inbox}:
      match ph:
        case Ch.Watching{w}:
          LLogicLogic.child.pc.absurd({ChS.St.placed(ChS.run([ChS.Reopen{}, ChS.Poll{d1, o1}, ChS.Poll{d2, o2}, ChS.Poll{d3, o3}, ChS.Deliver{m}], cfg, ChS.St{Ch.Watching{w}, cut, open, inbox})) == 1n : Nat}, ow)
        case Ch.Owing{+kr, +n}:
          match cut:
            case None{}:
              pc.ready_deliver(cfg, ChS.step(cfg, ChS.step(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), ChS.Poll{d2, o2}), ChS.Poll{d3, o3}), m, LA.pc.K_step(cfg, ChS.step(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), ChS.Poll{d2, o2}), ChS.Poll{d3, o3}, LA.pc.K_step(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), ChS.Poll{d2, o2}, LA.pc.K_step(cfg, ChS.St{Ch.Owing{kr, n}, None{}, True{}, inbox}, ChS.Poll{d1, o1}, k))), pc.ready_soon(cfg, ChS.step(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), ChS.Poll{d2, o2}), d3, o3, pc.soon_of_ready(ChS.step(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), ChS.Poll{d2, o2}), pc.ready_soon(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), d2, o2, pc.soon_owe(inbox, kr, n, LA.pc.and_l(LA.pc.Kowe(inbox, n), LA.pc.Kin(inbox), k), LA.pc.and_r(LA.pc.Kowe(inbox, n), LA.pc.Kin(inbox), k))))), em)
            case Some{del}:
              pc.ready_deliver(cfg, ChS.step(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), ChS.Poll{d3, o3}), m, LA.pc.K_step(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), ChS.Poll{d3, o3}, LA.pc.K_step(cfg, ChS.St{Ch.Owing{kr, n}, None{}, True{}, inbox}, ChS.Poll{d2, o2}, k)), pc.ready_soon(cfg, ChS.owe.do(Ch.owe.next(ChS.fate(inbox, n), n), kr, n, True{}, inbox), d3, o3, pc.soon_owe(inbox, kr, n, LA.pc.and_l(LA.pc.Kowe(inbox, n), LA.pc.Kin(inbox), k), LA.pc.and_r(LA.pc.Kowe(inbox, n), LA.pc.Kin(inbox), k))), em)
        case Ch.Ended{}:
          LLogicLogic.child.pc.absurd({ChS.St.placed(ChS.run([ChS.Reopen{}, ChS.Poll{d1, o1}, ChS.Poll{d2, o2}, ChS.Poll{d3, o3}, ChS.Deliver{m}], cfg, ChS.St{Ch.Ended{}, cut, open, inbox})) == 1n : Nat}, ow)

def pc.delivered_once(+cfg: Ch.Cfg, +w: Ch.W, +evs: List<&2, ChS.Ev>, +d1: Nat, +o1: Ch.Obs, +d2: Nat, +o2: Ch.Obs, +d3: Nat, +o3: Ch.Obs, ow: {ChS.owing(ChS.St.ph(ChS.run(evs, cfg, ChS.St.init(w)))) == True{} : Bool}, +m: Nat, em: {ChS.St.owed(ChS.run([ChS.Reopen{}, ChS.Poll{d1, o1}, ChS.Poll{d2, o2}, ChS.Poll{d3, o3}], cfg, ChS.run(evs, cfg, ChS.St.init(w)))) == m : Nat}) -> {ChS.St.placed(ChS.run([ChS.Reopen{}, ChS.Poll{d1, o1}, ChS.Poll{d2, o2}, ChS.Poll{d3, o3}, ChS.Deliver{m}], cfg, ChS.run(evs, cfg, ChS.St.init(w)))) == 1n : Nat}:
  pc.delivered(cfg, ChS.run(evs, cfg, ChS.St.init(w)), d1, o1, d2, o2, d3, o3, m, LA.pc.K_run(evs, cfg, ChS.St.init(w), {==}), ow, em)

def Child.child_delivered_once(cfg, w, evs, d1, o1, d2, o2, d3, o3, owing, m, waits):
  pc.delivered_once(cfg, w, evs, d1, o1, d2, o2, d3, o3, owing, m, waits)
