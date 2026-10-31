# eukhe: the proof of LAW best_never_worse
# The step's answer is the state after it (ar_after); by cases on the
# event: a refusal keeps the state; an init, a start, a line, a finish, a
# mode and every log but a keep append only rows that keep nothing
# (abandoned or not kept: AH.ah.last_ab, AH.ah.last_nk), so the best stays;
# a keep appends its metric x (AH.ah.last_keep), which beats every kept
# metric (keep.beats), so the last (AH.ah.beats_last); an init with a new
# segment moves the segment (excluded by `same`), a flag by `nf`.

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/segment.bend as SG
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ./base/history.bend as AH

# a keep's metric beats the last kept one
def ah.nw_bo(+c: ArS.Cfg, +x: ArD.Dec, b: Maybe<&2, ArD.Dec>, h: {ArS.beats.at(ArS.Cfg.dir(c), x, b) == True{} : Bool}) -> AutoresearchHistory.ar_better.of(Some{c}, Some{x}, b):
  match b:
    case None{}:
      Unit{}
    case Some{y}:
      Equal.trans(Bool, SG.is_better(~ArD.Dec.cmp, ArS.Cfg.dir(c), x, y), ArS.better(ArS.Cfg.dir(c), x, y), True{}, Equal.sym(Bool, ArS.better(ArS.Cfg.dir(c), x, y), SG.is_better(~ArD.Dec.cmp, ArS.Cfg.dir(c), x, y), AH.ah.better_sg(ArS.Cfg.dir(c), x, y)), h)

def ah.nw_better(+c: ArS.Cfg, +x: ArD.Dec, +seg: Nat, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == Some{x} : Maybe<&2, ArD.Dec>}, eqb: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == True{} : Bool}) -> AutoresearchHistory.ar_better.of(Some{c}, ArS.last(ArS.snoc(runs, [ArS.row(ArS.primary(Some{c}), seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)]), seg), ArS.last(runs, seg)):
  +eqm2 = Equal.trans(Maybe<&2, ArD.Dec>, ArS.lookup(kvs, ArS.primary(Some{c})), ArS.lookup(kvs, ArS.Cfg.metric(c)), Some{x}, Equal.cong(String, Maybe<&2, ArD.Dec>, k => ArS.lookup(kvs, k), ArS.primary(Some{c}), ArS.Cfg.metric(c), AH.ah.prim(c)), eqm)
  %Equal.sym(Maybe<&2, ArD.Dec>, ArS.last(ArS.snoc(runs, [ArS.row(ArS.primary(Some{c}), seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)]), seg), Some{x}, AH.ah.last_keep(runs, id, seg, kvs, fin, desc, ArS.primary(Some{c}), x, eqm2)) : AutoresearchHistory.ar_better.of(Some{c}, _, ArS.last(runs, seg))
  ah.nw_bo(c, x, ArS.last(runs, seg), AH.ah.beats_last(ArS.Cfg.dir(c), x, runs, seg, eqb))

def ah.nw_why(ok: Bool, +c: ArS.Cfg, +x: ArD.Dec, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == Some{x} : Maybe<&2, ArD.Dec>}, eqb: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == True{} : Bool}) -> AutoresearchHistory.ar_not_worse(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, ArM.ar_after(ArP.keep.why(ok, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc), ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}})):
  match ok:
    case True{}:
      Inr{ah.nw_better(c, x, seg, runs, id, kvs, fin, desc, eqm, eqb)}
    case False{}:
      Inl{{==}}

def ah.nw_beats(ok: Bool, +c: ArS.Cfg, +x: ArD.Dec, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == Some{x} : Maybe<&2, ArD.Dec>}, eqb: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == ok : Bool}) -> AutoresearchHistory.ar_not_worse(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, ArM.ar_after(ArP.keep.beats(ok, x, ArS.Cfg.dir(c), why, devs, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc), ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}})):
  match ok:
    case True{}:
      ah.nw_why(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), c, x, seg, mode, runs, id, kvs, fin, desc, eqm, eqb)
    case False{}:
      Inl{{==}}

def ah.nw_metric(m: Maybe<&2, ArD.Dec>, +c: ArS.Cfg, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == m : Maybe<&2, ArD.Dec>}) -> AutoresearchHistory.ar_not_worse(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, ArM.ar_after(ArP.keep.metric(m, c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc), ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}})):
  match m:
    case None{}:
      Inl{{==}}
    case Some{+x}:
      ah.nw_beats(ArS.beats(ArS.Cfg.dir(c), x, runs, seg), c, x, why, devs, seg, mode, runs, id, kvs, fin, desc, eqm, {==})

def ah.nw_line(m: Maybe<&2, ArL.Kv>, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>) -> AutoresearchHistory.ar_not_worse(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArM.ar_after(ArP.line.got(m, cfg, seg, mode, runs, id, kvs), ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}})):
  match m:
    case None{}:
      Inl{{==}}
    case Some{kv}:
      match kv:
        case ArL.Kv{n, d}:
          Inl{{==}}

def ah.nw_begin(ok: Bool, +n: Nat, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> AutoresearchHistory.ar_not_worse(ArS.St{Some{c}, seg, mode, runs, pend}, ArM.ar_after(ArP.begin.at(ok, n, c, seg, mode, runs, pend), ArS.St{Some{c}, seg, mode, runs, pend})):
  match ok:
    case True{}:
      Inl{AH.ah.last_ab(runs, ArS.Cfg.metric(c), seg, pend, seg)}
    case False{}:
      Inl{{==}}

def ah.nw_same(ok: Bool, +c: ArS.Cfg, +m: String, +old: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> AutoresearchHistory.ar_not_worse(ArS.St{old, seg, mode, runs, pend}, ArM.ar_after(ArP.init.keep(ok, c, m, seg, runs, pend), ArS.St{old, seg, mode, runs, pend})):
  match ok:
    case True{}:
      Inl{AH.ah.last_ab(runs, m, seg, pend, seg)}
    case False{}:
      Inl{{==}}

def ah.nw_init(er: Maybe<&2, String>, old: Maybe<&2, ArS.Cfg>, fresh: Bool, harness: Bool, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, same: {ArM.ar_seg(ArM.ar_after(ArP.init.check(er, old, c, fresh, harness, seg, runs, pend), ArS.St{old, seg, mode, runs, pend})) == seg : Nat}) -> AutoresearchHistory.ar_not_worse(ArS.St{old, seg, mode, runs, pend}, ArM.ar_after(ArP.init.check(er, old, c, fresh, harness, seg, runs, pend), ArS.St{old, seg, mode, runs, pend})):
  match er:
    case Some{t}:
      Inl{{==}}
    case None{}:
      match old:
        case None{}:
          match harness:
            case True{}:
              Inl{AH.ah.last_ab(runs, "", seg, pend, seg)}
            case False{}:
              Inl{{==}}
        case Some{+o}:
          match fresh:
            case True{}:
              match harness:
                case True{}:
                  AH.ah.nsucc(AutoresearchHistory.ar_not_worse(ArS.St{Some{o}, seg, mode, runs, pend}, ArS.St{Some{c}, 1n+seg, ArS.On{}, ArS.snoc(runs, ArS.abandon(ArS.Cfg.metric(o), seg, pend)), None{}}), seg, same)
                case False{}:
                  Inl{{==}}
            case False{}:
              ah.nw_same(ArP.same(o, c), c, ArS.Cfg.metric(o), Some{o}, seg, mode, runs, pend)

# the claim for a step's answer r on state s
def ah.NW(+s: ArS.St, r: ArS.Res) -> Type:
  AutoresearchHistory.ar_not_worse(s, ArM.ar_after(r, s))

def ah.nw_begin0(cfg: Maybe<&2, ArS.Cfg>, +n: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> ah.NW(ArS.St{cfg, seg, mode, runs, pend}, ArP.begin(ArS.St{cfg, seg, mode, runs, pend}, n)):
  match cfg:
    case None{}:
      Inl{{==}}
    case Some{+c}:
      +k = {1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)) : Nat}
      ah.nw_begin(Nat.is_eq(n, k), k, c, seg, mode, runs, pend)

def ah.nw_line0(pend: Maybe<&2, ArS.Pend>, +text: String, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>) -> ah.NW(ArS.St{cfg, seg, mode, runs, pend}, ArP.line(ArS.St{cfg, seg, mode, runs, pend}, text)):
  match pend:
    case None{}:
      Inl{{==}}
    case Some{q}:
      match q:
        case ArS.Pend{+id, +kvs, fin}:
          match fin:
            case Some{p}:
              Inl{{==}}
            case None{}:
              ah.nw_line(ArL.metric(text), cfg, seg, mode, runs, id, kvs)

def ah.nw_fin0(pend: Maybe<&2, ArS.Pend>, -neg: Bool, -code: Nat, -timeout: Bool, -cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>) -> ah.NW(ArS.St{cfg, seg, mode, runs, pend}, ArP.finish(ArS.St{cfg, seg, mode, runs, pend}, neg, code, timeout)):
  match pend:
    case None{}:
      Inl{{==}}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case Some{p}:
              Inl{{==}}
            case None{}:
              Inl{{==}}

def ah.nw_log(pend: Maybe<&2, ArS.Pend>, st: ArS.Status, cfg: Maybe<&2, ArS.Cfg>, +desc: String, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>) -> ah.NW(ArS.St{cfg, seg, mode, runs, pend}, ArP.log(ArS.St{cfg, seg, mode, runs, pend}, st, desc, why, devs)):
  match pend:
    case None{}:
      Inl{{==}}
    case Some{q}:
      match q:
        case ArS.Pend{+id, +kvs, fin}:
          match fin:
            case None{}:
              Inl{{==}}
            case Some{passed}:
              match passed:
                case True{}:
                  match st:
                    case ArS.Keep{}:
                      match cfg:
                        case None{}:
                          Inl{{==}}
                        case Some{+c}:
                          ah.nw_metric(ArS.lookup(kvs, ArS.Cfg.metric(c)), c, why, devs, seg, mode, runs, id, kvs, Some{True{}}, desc, {==})
                    case ArS.Discard{}:
                      Inl{AH.ah.last_nk(runs, ArS.primary(cfg), seg, ArS.Pend{id, kvs, Some{True{}}}, ArS.Discard{}, desc, seg, {==})}
                    case ArS.Crash{}:
                      Inl{{==}}
                    case ArS.Checks{}:
                      Inl{AH.ah.last_nk(runs, ArS.primary(cfg), seg, ArS.Pend{id, kvs, Some{True{}}}, ArS.Checks{}, desc, seg, {==})}
                case False{}:
                  match st:
                    case ArS.Keep{}:
                      Inl{{==}}
                    case ArS.Discard{}:
                      Inl{AH.ah.last_nk(runs, ArS.primary(cfg), seg, ArS.Pend{id, kvs, Some{False{}}}, ArS.Discard{}, desc, seg, {==})}
                    case ArS.Crash{}:
                      Inl{AH.ah.last_nk(runs, ArS.primary(cfg), seg, ArS.Pend{id, kvs, Some{False{}}}, ArS.Crash{}, desc, seg, {==})}
                    case ArS.Checks{}:
                      Inl{{==}}

def ah.nw(s: ArS.St, e: ArS.Ev, nf: {ArM.ar_is_flag(e) == False{} : Bool}, same: {ArM.ar_seg(ArM.ar_after(ArP.step(s, e), s)) == ArM.ar_seg(s) : Nat}) -> AutoresearchHistory.ar_not_worse(s, ArM.ar_after(ArP.step(s, e), s)):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, +pend}:
      match e:
        case ArS.Init{+c, fresh, harness}:
          ah.nw_init(ArP.init.err(c), cfg, fresh, harness, c, seg, mode, runs, pend, same)
        case ArS.Begin{+n}:
          ah.nw_begin0(cfg, n, seg, mode, runs, pend)
        case ArS.Line{text}:
          ah.nw_line0(pend, text, cfg, seg, mode, runs)
        case ArS.Finish{neg, code, timeout}:
          ah.nw_fin0(pend, neg, code, timeout, cfg, seg, mode, runs)
        case ArS.Log{st, desc, why, devs}:
          ah.nw_log(pend, st, cfg, desc, why, devs, seg, mode, runs)
        case ArS.Flag{n, r}:
          AH.ah.absurdT(AutoresearchHistory.ar_not_worse(ArS.St{cfg, seg, mode, runs, pend}, ArM.ar_after(ArP.step(ArS.St{cfg, seg, mode, runs, pend}, ArS.Flag{n, r}), ArS.St{cfg, seg, mode, runs, pend})), nf)
        case ArS.SetMode{m}:
          Inl{{==}}

def AutoresearchHistory.best_never_worse(s, e, s2, eff, stop, ok, nf, same):
  +ea = Equal.cong(ArS.Res, ArS.St, r => ArM.ar_after(r, s), ArP.step(s, e), ArS.Took{s2, eff, stop}, ok)
  %ea : AutoresearchHistory.ar_not_worse(s, _)
  ah.nw(s, e, nf, Equal.trans(Nat, ArM.ar_seg(ArM.ar_after(ArP.step(s, e), s)), ArM.ar_seg(s2), ArM.ar_seg(s), Equal.cong(ArS.St, Nat, ArM.ar_seg, ArM.ar_after(ArP.step(s, e), s), s2, ea), same))
