# eukhe: the proof of LAW run_conservation
# By induction over the history, from any state whose ids are runs 1..K
# (K: the rows and the pending run, ArS.St.started): each step keeps that
# and adds to K one exactly for an accepted start (ah.rc): a start takes
# id 1 + K and moves the pending run to the rows; an init or a log moves
# it to the rows; a flag keeps the rows' ids and number; the other steps
# keep the rows. So K after the history is the accepted starts, and the
# logged and abandoned rows plus the pending run are K (AR.ah.count).

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ./base/history.bend as AH
import ./best_is_best/order.bend as AO
import ./run_conservation/ids.bend as AR

# the ids of s are runs 1..K
def ah.HI(s: ArS.St) -> Data:
  {AutoresearchHistory.ar_ids(s) == AutoresearchHistory.ar_upto(AR.ah.K(s)) : List<&2, Nat>}

# after the answer r of a step on s (a start when b): K grows by one for
# an accepted start, and the ids are runs 1..K
def ah.RS(+s: ArS.St, +b: Bool, r: ArS.Res) -> Type:
  {AR.ah.K(ArM.ar_after(r, s)) == Nat.add(ArM.ar_one(Bool.and(b, ArM.ar_took(r))), AR.ah.K(s)) : Nat} & ah.HI(ArM.ar_after(r, s))

def ah.rs_k(-s: ArS.St, -b: Bool, -r: ArS.Res, p: ah.RS(s, b, r)) -> {AR.ah.K(ArM.ar_after(r, s)) == Nat.add(ArM.ar_one(Bool.and(b, ArM.ar_took(r))), AR.ah.K(s)) : Nat}:
  (k, i) = p
  k

def ah.rs_i(-s: ArS.St, -b: Bool, -r: ArS.Res, p: ah.RS(s, b, r)) -> ah.HI(ArM.ar_after(r, s)):
  (k, i) = p
  i

# same count and ids
def ah.rc_eq(-s: ArS.St, -s2: ArS.St, +hk: {AR.ah.K(s2) == AR.ah.K(s) : Nat}, hid: {AutoresearchHistory.ar_ids(s2) == AutoresearchHistory.ar_ids(s) : List<&2, Nat>}, hi: ah.HI(s)) -> {AR.ah.K(s2) == AR.ah.K(s) : Nat} & ah.HI(s2):
  (hk, Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids(s2), AutoresearchHistory.ar_ids(s), AutoresearchHistory.ar_upto(AR.ah.K(s2)), hid, Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids(s), AutoresearchHistory.ar_upto(AR.ah.K(s)), AutoresearchHistory.ar_upto(AR.ah.K(s2)), hi, Equal.cong(Nat, List<&2, Nat>, AutoresearchHistory.ar_upto, AR.ah.K(s), AR.ah.K(s2), Equal.sym(Nat, AR.ah.K(s2), AR.ah.K(s), hk)))))

# The steps
# ---------

# the pending run moved to the rows, abandoned
def ah.rc_ab(-cfg2: Maybe<&2, ArS.Cfg>, -seg2: Nat, -mode2: ArS.Mode, +m: String, -cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend})) -> {AR.ah.K(ArS.St{cfg2, seg2, mode2, ArS.snoc(runs, ArS.abandon(m, seg, pend)), None{}}) == AR.ah.K(ArS.St{cfg, seg, mode, runs, pend}) : Nat} & ah.HI(ArS.St{cfg2, seg2, mode2, ArS.snoc(runs, ArS.abandon(m, seg, pend)), None{}}):
  +ab = ArS.abandon(m, seg, pend)
  +hk = Equal.trans(Nat, Nat.add(ArS.rlen(ArS.snoc(runs, ab)), 0n), ArS.rlen(ArS.snoc(runs, ab)), Nat.add(ArS.rlen(runs), ArS.pcount(pend)), AH.ah.add_zero(ArS.rlen(ArS.snoc(runs, ab))), Equal.trans(Nat, ArS.rlen(ArS.snoc(runs, ab)), Nat.add(ArS.rlen(runs), ArS.rlen(ab)), Nat.add(ArS.rlen(runs), ArS.pcount(pend)), AR.ah.rlen_snoc(runs, ab), Equal.cong(Nat, Nat, x => Nat.add(ArS.rlen(runs), x), ArS.rlen(ab), ArS.pcount(pend), AR.ah.rlen_ab(m, seg, pend))))
  +hid = Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids.rows(ArS.snoc(runs, ab), Nil{}), AutoresearchHistory.ar_ids.rows(runs, AutoresearchHistory.ar_ids.rows(ab, Nil{})), AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), AR.ah.ids_snoc(runs, ab, Nil{}), Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids.rows(runs, AutoresearchHistory.ar_ids.rows(ab, Nil{})), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), Equal.cong(List<&2, Nat>, List<&2, Nat>, x => AutoresearchHistory.ar_ids.rows(runs, x), AutoresearchHistory.ar_ids.rows(ab, Nil{}), AR.ah.tl(pend), AR.ah.ids_ab0(m, seg, pend)), Equal.sym(List<&2, Nat>, AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AR.ah.ids_tl(cfg, seg, mode, runs, pend))))
  ah.rc_eq(ArS.St{cfg, seg, mode, runs, pend}, ArS.St{cfg2, seg2, mode2, ArS.snoc(runs, ab), None{}}, hk, hid, hi)

def ah.rc_keep(ok: Bool, -c: ArS.Cfg, +m: String, -old: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{old, seg, mode, runs, pend})) -> ah.RS(ArS.St{old, seg, mode, runs, pend}, False{}, ArP.init.keep(ok, c, m, seg, runs, pend)):
  match ok:
    case True{}:
      ah.rc_ab(Some{c}, seg, ArS.On{}, m, old, seg, mode, runs, pend, hi)
    case False{}:
      ({==}, hi)

def ah.rc_init(er: Maybe<&2, String>, old: Maybe<&2, ArS.Cfg>, fresh: Bool, harness: Bool, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{old, seg, mode, runs, pend})) -> ah.RS(ArS.St{old, seg, mode, runs, pend}, False{}, ArP.init.check(er, old, c, fresh, harness, seg, runs, pend)):
  match er:
    case Some{t}:
      ({==}, hi)
    case None{}:
      match old:
        case None{}:
          match harness:
            case True{}:
              ah.rc_ab(Some{c}, seg, ArS.On{}, "", None{}, seg, mode, runs, pend, hi)
            case False{}:
              ({==}, hi)
        case Some{+o}:
          match fresh:
            case True{}:
              match harness:
                case True{}:
                  ah.rc_ab(Some{c}, 1n+seg, ArS.On{}, ArS.Cfg.metric(o), Some{o}, seg, mode, runs, pend, hi)
                case False{}:
                  ({==}, hi)
            case False{}:
              ah.rc_keep(ArP.same(o, c), c, ArS.Cfg.metric(o), Some{o}, seg, mode, runs, pend, hi)

# an accepted start: id 1 + K
def ah.rc_begin(ok: Bool, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{Some{c}, seg, mode, runs, pend})) -> ah.RS(ArS.St{Some{c}, seg, mode, runs, pend}, True{}, ArP.begin.at(ok, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), c, seg, mode, runs, pend)):
  match ok:
    case False{}:
      ({==}, hi)
    case True{}:
      +m = ArS.Cfg.metric(c)
      +ab = ArS.abandon(m, seg, pend)
      +k0 = Nat.add(ArS.rlen(runs), ArS.pcount(pend))
      +k = {1n+k0 : Nat}
      +s2 = {ArS.St{Some{c}, seg, mode, ArS.snoc(runs, ab), Some{ArS.Pend{k, Nil{}, None{}}}} : ArS.St}
      +kE = Equal.trans(Nat, Nat.add(ArS.rlen(ArS.snoc(runs, ab)), 1n), Nat.add(Nat.add(ArS.rlen(runs), ArS.rlen(ab)), 1n), k, Equal.cong(Nat, Nat, x => Nat.add(x, 1n), ArS.rlen(ArS.snoc(runs, ab)), Nat.add(ArS.rlen(runs), ArS.rlen(ab)), AR.ah.rlen_snoc(runs, ab)), Equal.trans(Nat, Nat.add(Nat.add(ArS.rlen(runs), ArS.rlen(ab)), 1n), Nat.add(k0, 1n), k, Equal.cong(Nat, Nat, x => Nat.add(Nat.add(ArS.rlen(runs), x), 1n), ArS.rlen(ab), ArS.pcount(pend), AR.ah.rlen_ab(m, seg, pend)), AR.ah.add_one(k0)))
      +hi2 = Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AutoresearchHistory.ar_ids(ArS.St{Some{c}, seg, mode, runs, pend}), AutoresearchHistory.ar_upto(k0), Equal.sym(List<&2, Nat>, AutoresearchHistory.ar_ids(ArS.St{Some{c}, seg, mode, runs, pend}), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AR.ah.ids_tl(Some{c}, seg, mode, runs, pend)), hi)
      +e1 = AR.ah.ids_snoc(runs, ab, [k])
      +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, x => AutoresearchHistory.ar_ids.rows(runs, x), AutoresearchHistory.ar_ids.rows(ab, [k]), List.append(&2, Nat, AR.ah.tl(pend), [k]), AR.ah.ids_ab(m, seg, pend, [k]))
      +e3 = AR.ah.ids_app(runs, AR.ah.tl(pend), [k])
      +e4 = Equal.cong(List<&2, Nat>, List<&2, Nat>, x => List.append(&2, Nat, x, [k]), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AutoresearchHistory.ar_upto(k0), hi2)
      +e5 = Equal.sym(List<&2, Nat>, AutoresearchHistory.ar_upto.go(k0, [k]), List.append(&2, Nat, AutoresearchHistory.ar_upto.go(k0, Nil{}), [k]), AR.ah.upto_app(k0, Nil{}, [k]))
      +e6 = Equal.cong(Nat, List<&2, Nat>, AutoresearchHistory.ar_upto, k, AR.ah.K(s2), Equal.sym(Nat, AR.ah.K(s2), k, kE))
      +e56 = Equal.trans(List<&2, Nat>, List.append(&2, Nat, AutoresearchHistory.ar_upto(k0), [k]), AutoresearchHistory.ar_upto(k), AutoresearchHistory.ar_upto(AR.ah.K(s2)), e5, e6)
      +e456 = Equal.trans(List<&2, Nat>, List.append(&2, Nat, AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), [k]), List.append(&2, Nat, AutoresearchHistory.ar_upto(k0), [k]), AutoresearchHistory.ar_upto(AR.ah.K(s2)), e4, e56)
      +e3456 = Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids.rows(runs, List.append(&2, Nat, AR.ah.tl(pend), [k])), List.append(&2, Nat, AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), [k]), AutoresearchHistory.ar_upto(AR.ah.K(s2)), e3, e456)
      +e23456 = Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids.rows(runs, AutoresearchHistory.ar_ids.rows(ab, [k])), AutoresearchHistory.ar_ids.rows(runs, List.append(&2, Nat, AR.ah.tl(pend), [k])), AutoresearchHistory.ar_upto(AR.ah.K(s2)), e2, e3456)
      (kE, Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids.rows(ArS.snoc(runs, ab), [k]), AutoresearchHistory.ar_ids.rows(runs, AutoresearchHistory.ar_ids.rows(ab, [k])), AutoresearchHistory.ar_upto(AR.ah.K(s2)), e1, e23456))

def ah.rc_begin0(cfg: Maybe<&2, ArS.Cfg>, +n: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend})) -> ah.RS(ArS.St{cfg, seg, mode, runs, pend}, True{}, ArP.begin(ArS.St{cfg, seg, mode, runs, pend}, n)):
  match cfg:
    case None{}:
      ({==}, hi)
    case Some{+c}:
      ah.rc_begin(Nat.is_eq(n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))), c, seg, mode, runs, pend, hi)

def ah.rc_line(m: Maybe<&2, ArL.Kv>, -cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, -id: Nat, -kvs: List<&2, ArL.Kv>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}})) -> ah.RS(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, False{}, ArP.line.got(m, cfg, seg, mode, runs, id, kvs)):
  match m:
    case None{}:
      ({==}, hi)
    case Some{kv}:
      match kv:
        case ArL.Kv{n, d}:
          ({==}, hi)

def ah.rc_line0(pend: Maybe<&2, ArS.Pend>, +text: String, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend})) -> ah.RS(ArS.St{cfg, seg, mode, runs, pend}, False{}, ArP.line(ArS.St{cfg, seg, mode, runs, pend}, text)):
  match pend:
    case None{}:
      ({==}, hi)
    case Some{q}:
      match q:
        case ArS.Pend{+id, +kvs, fin}:
          match fin:
            case Some{p}:
              ({==}, hi)
            case None{}:
              ah.rc_line(ArL.metric(text), cfg, seg, mode, runs, id, kvs, hi)

def ah.rc_fin0(pend: Maybe<&2, ArS.Pend>, -neg: Bool, -code: Nat, -timeout: Bool, -cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend})) -> ah.RS(ArS.St{cfg, seg, mode, runs, pend}, False{}, ArP.finish(ArS.St{cfg, seg, mode, runs, pend}, neg, code, timeout)):
  match pend:
    case None{}:
      ({==}, hi)
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case Some{p}:
              ({==}, hi)
            case None{}:
              ({==}, hi)

# a logged run moves to the rows
def ah.rc_done(+cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +st: ArS.Status, +desc: String, -eff: ArS.Eff, hi: ah.HI(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}})) -> ah.RS(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, False{}, ArP.log.done(cfg, seg, mode, runs, ArS.Pend{id, kvs, fin}, st, desc, eff)):
  +r = ArS.row(ArS.primary(cfg), seg, ArS.Pend{id, kvs, fin}, Some{st}, desc)
  +runs2 = ArS.snoc(runs, [r])
  +hk = Equal.trans(Nat, Nat.add(ArS.rlen(runs2), 0n), ArS.rlen(runs2), Nat.add(ArS.rlen(runs), 1n), AH.ah.add_zero(ArS.rlen(runs2)), AR.ah.rlen_snoc(runs, [r]))
  ah.rc_eq(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, ArS.St{cfg, seg, ArP.log.mode(ArP.capped(cfg, ArS.logged(runs2, seg)), mode), runs2, None{}}, hk, AR.ah.ids_snoc(runs, [r], Nil{}), hi)

def ah.rc_why(ok: Bool, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, hi: ah.HI(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}})) -> ah.RS(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, False{}, ArP.keep.why(ok, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc)):
  match ok:
    case True{}:
      ah.rc_done(Some{c}, seg, mode, runs, id, kvs, fin, ArS.Keep{}, desc, ArS.Commit{}, hi)
    case False{}:
      ({==}, hi)

def ah.rc_beats(ok: Bool, +c: ArS.Cfg, -x: ArD.Dec, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, hi: ah.HI(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}})) -> ah.RS(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, False{}, ArP.keep.beats(ok, x, ArS.Cfg.dir(c), why, devs, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc)):
  match ok:
    case True{}:
      ah.rc_why(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), c, seg, mode, runs, id, kvs, fin, desc, hi)
    case False{}:
      ({==}, hi)

def ah.rc_metric(m: Maybe<&2, ArD.Dec>, +c: ArS.Cfg, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, hi: ah.HI(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}})) -> ah.RS(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, False{}, ArP.keep.metric(m, c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc)):
  match m:
    case None{}:
      ({==}, hi)
    case Some{+x}:
      ah.rc_beats(ArS.beats(ArS.Cfg.dir(c), x, runs, seg), c, x, why, devs, seg, mode, runs, id, kvs, fin, desc, hi)

def ah.rc_log0(pend: Maybe<&2, ArS.Pend>, st: ArS.Status, cfg: Maybe<&2, ArS.Cfg>, +desc: String, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend})) -> ah.RS(ArS.St{cfg, seg, mode, runs, pend}, False{}, ArP.log(ArS.St{cfg, seg, mode, runs, pend}, st, desc, why, devs)):
  match pend:
    case None{}:
      ({==}, hi)
    case Some{q}:
      match q:
        case ArS.Pend{+id, +kvs, fin}:
          match fin:
            case None{}:
              ({==}, hi)
            case Some{passed}:
              match passed:
                case True{}:
                  match st:
                    case ArS.Keep{}:
                      match cfg:
                        case None{}:
                          ({==}, hi)
                        case Some{+c}:
                          ah.rc_metric(ArS.lookup(kvs, ArS.Cfg.metric(c)), c, why, devs, seg, mode, runs, id, kvs, Some{True{}}, desc, hi)
                    case ArS.Discard{}:
                      ah.rc_done(cfg, seg, mode, runs, id, kvs, Some{True{}}, ArS.Discard{}, desc, ArS.Reset{}, hi)
                    case ArS.Crash{}:
                      ({==}, hi)
                    case ArS.Checks{}:
                      ah.rc_done(cfg, seg, mode, runs, id, kvs, Some{True{}}, ArS.Checks{}, desc, ArS.Reset{}, hi)
                case False{}:
                  match st:
                    case ArS.Keep{}:
                      ({==}, hi)
                    case ArS.Discard{}:
                      ah.rc_done(cfg, seg, mode, runs, id, kvs, Some{False{}}, ArS.Discard{}, desc, ArS.Reset{}, hi)
                    case ArS.Crash{}:
                      ah.rc_done(cfg, seg, mode, runs, id, kvs, Some{False{}}, ArS.Crash{}, desc, ArS.Reset{}, hi)
                    case ArS.Checks{}:
                      ({==}, hi)

def ah.rc_end(f: Bool, +a: List<&2, ArS.Row>, -n: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend}), hl: {ArS.rlen(a) == ArS.rlen(runs) : Nat}, hid: {AutoresearchHistory.ar_ids.rows(a, AR.ah.tl(pend)) == AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)) : List<&2, Nat>}) -> ah.RS(ArS.St{cfg, seg, mode, runs, pend}, False{}, ArP.flag.end(f, n, cfg, seg, mode, a, pend)):
  match f:
    case True{}:
      +hid2 = Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, a, pend}), AutoresearchHistory.ar_ids.rows(a, AR.ah.tl(pend)), AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), AR.ah.ids_tl(cfg, seg, mode, a, pend), Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids.rows(a, AR.ah.tl(pend)), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), hid, Equal.sym(List<&2, Nat>, AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AR.ah.ids_tl(cfg, seg, mode, runs, pend))))
      ah.rc_eq(ArS.St{cfg, seg, mode, runs, pend}, ArS.St{cfg, seg, mode, a, pend}, Equal.cong(Nat, Nat, x => Nat.add(x, ArS.pcount(pend)), ArS.rlen(a), ArS.rlen(runs), hl), hid2, hi)
    case False{}:
      ({==}, hi)

def ah.rc_found(q: List<&2, ArS.Row> & Bool, +n: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend}), hl: {ArS.rlen(AO.ah.fst(q)) == ArS.rlen(runs) : Nat}, hid: {AutoresearchHistory.ar_ids.rows(AO.ah.fst(q), AR.ah.tl(pend)) == AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)) : List<&2, Nat>}) -> ah.RS(ArS.St{cfg, seg, mode, runs, pend}, False{}, ArP.flag.found(q, n, cfg, seg, mode, pend)):
  (a, f) = q
  ah.rc_end(f, a, n, cfg, seg, mode, runs, pend, hi, hl, hid)

def ah.rc_flag(ok: Bool, +n: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hi: ah.HI(ArS.St{cfg, seg, mode, runs, pend})) -> ah.RS(ArS.St{cfg, seg, mode, runs, pend}, False{}, ArP.flag.reason(ok, ArS.St{cfg, seg, mode, runs, pend}, n)):
  match ok:
    case True{}:
      ah.rc_found(ArP.flag.rows(runs, n), n, cfg, seg, mode, runs, pend, hi, AR.ah.flag_rlen(runs, n), AR.ah.flag_ids(runs, n, AR.ah.tl(pend)))
    case False{}:
      ({==}, hi)

# one step keeps the ids runs 1..K, and K counts the accepted starts
def ah.rc(s: ArS.St, e: ArS.Ev, hi: ah.HI(s)) -> ah.RS(s, ArM.ar_is_begin(e), ArP.step(s, e)):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, +pend}:
      match e:
        case ArS.Init{+c, fresh, harness}:
          ah.rc_init(ArP.init.err(c), cfg, fresh, harness, c, seg, mode, runs, pend, hi)
        case ArS.Begin{+n}:
          ah.rc_begin0(cfg, n, seg, mode, runs, pend, hi)
        case ArS.Line{text}:
          ah.rc_line0(pend, text, cfg, seg, mode, runs, hi)
        case ArS.Finish{neg, code, timeout}:
          ah.rc_fin0(pend, neg, code, timeout, cfg, seg, mode, runs, hi)
        case ArS.Log{st, desc, why, devs}:
          ah.rc_log0(pend, st, cfg, desc, why, devs, seg, mode, runs, hi)
        case ArS.Flag{+n, reason}:
          ah.rc_flag(ArL.some(reason), n, cfg, seg, mode, runs, pend, hi)
        case ArS.SetMode{m}:
          ah.rc_eq(ArS.St{cfg, seg, mode, runs, pend}, ArS.St{cfg, seg, m, runs, pend}, {==}, Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids(ArS.St{cfg, seg, m, runs, pend}), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), AR.ah.ids_tl(cfg, seg, m, runs, pend), Equal.sym(List<&2, Nat>, AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}), AutoresearchHistory.ar_ids.rows(runs, AR.ah.tl(pend)), AR.ah.ids_tl(cfg, seg, mode, runs, pend))), hi)

# Histories
# ---------

def ah.G(evs: List<&2, ArS.Ev>, +s: ArS.St) -> Type:
  {AR.ah.K(ArM.ar_run.go(evs, s)) == Nat.add(AutoresearchHistory.ar_starts.go(evs, s), AR.ah.K(s)) : Nat} & ah.HI(ArM.ar_run.go(evs, s))

def ah.g_k(-evs: List<&2, ArS.Ev>, -s: ArS.St, p: ah.G(evs, s)) -> {AR.ah.K(ArM.ar_run.go(evs, s)) == Nat.add(AutoresearchHistory.ar_starts.go(evs, s), AR.ah.K(s)) : Nat}:
  (k, i) = p
  k

def ah.g_i(-evs: List<&2, ArS.Ev>, -s: ArS.St, p: ah.G(evs, s)) -> ah.HI(ArM.ar_run.go(evs, s)):
  (k, i) = p
  i

def ah.rc_go(evs: List<&2, ArS.Ev>, +s: ArS.St, +hi: ah.HI(s)) -> ah.G(evs, s):
  match evs:
    case Nil{}:
      ({==}, hi)
    case +e <> +t:
      +s2 = ArM.ar_after(ArP.step(s, e), s)
      +hi2 = ah.rs_i(s, ArM.ar_is_begin(e), ArP.step(s, e), ah.rc(s, e, hi))
      +b = Bool.and(ArM.ar_is_begin(e), ArM.ar_took(ArP.step(s, e)))
      +g = AutoresearchHistory.ar_starts.go(t, s2)
      (Equal.trans(Nat, AR.ah.K(ArM.ar_run.go(t, s2)), Nat.add(g, AR.ah.K(s2)), Nat.add(Nat.add(ArM.ar_one(b), g), AR.ah.K(s)), ah.g_k(t, s2, ah.rc_go(t, s2, hi2)), Equal.trans(Nat, Nat.add(g, AR.ah.K(s2)), Nat.add(g, Nat.add(ArM.ar_one(b), AR.ah.K(s))), Nat.add(Nat.add(ArM.ar_one(b), g), AR.ah.K(s)), Equal.cong(Nat, Nat, x => Nat.add(g, x), AR.ah.K(s2), Nat.add(ArM.ar_one(b), AR.ah.K(s)), ah.rs_k(s, ArM.ar_is_begin(e), ArP.step(s, e), ah.rc(s, e, hi))), AR.ah.swap(b, g, AR.ah.K(s)))), ah.g_i(t, s2, ah.rc_go(t, s2, hi2)))

def AutoresearchHistory.run_conservation(evs):
  +kk = Equal.trans(Nat, AR.ah.K(ArM.ar_run(evs)), Nat.add(AutoresearchHistory.ar_starts(evs), 0n), AutoresearchHistory.ar_starts(evs), ah.g_k(evs, ArS.St.empty(), ah.rc_go(evs, ArS.St.empty(), {==})), AH.ah.add_zero(AutoresearchHistory.ar_starts(evs)))
  (Equal.trans(List<&2, Nat>, AutoresearchHistory.ar_ids(ArM.ar_run(evs)), AutoresearchHistory.ar_upto(AR.ah.K(ArM.ar_run(evs))), AutoresearchHistory.ar_upto(AutoresearchHistory.ar_starts(evs)), ah.g_i(evs, ArS.St.empty(), ah.rc_go(evs, ArS.St.empty(), {==})), Equal.cong(Nat, List<&2, Nat>, AutoresearchHistory.ar_upto, AR.ah.K(ArM.ar_run(evs)), AutoresearchHistory.ar_starts(evs), kk)), Equal.trans(Nat, Nat.add(AutoresearchHistory.ar_status_n(ArM.ar_runs(ArM.ar_run(evs)), True{}), Nat.add(AutoresearchHistory.ar_status_n(ArM.ar_runs(ArM.ar_run(evs)), False{}), AutoresearchHistory.ar_pending_n(ArM.ar_run(evs)))), AR.ah.K(ArM.ar_run(evs)), AutoresearchHistory.ar_starts(evs), AR.ah.count(ArM.ar_run(evs)), kk))
