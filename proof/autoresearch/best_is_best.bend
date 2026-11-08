# eukhe: the proof of LAW best_is_best
# An invariant of every state a history reaches from the empty one
# (ah.Inv): without a configuration there are no runs and no pending run;
# with one, the segment's kept metrics are in order, each better than
# every earlier one (AO.ah.ord, in the direction of the configuration),
# and no row is of a later segment (AO.ah.below). Every step keeps it: rows
# that keep nothing keep the order, a keep beats every kept metric, a flag
# only drops kept metrics, an init with a new segment leaves no row kept
# in it, one on the same segment keeps the direction. In order, the last
# kept metric is the segment's best (AB.ah.best).

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ./base/history.bend as AH
import ./best_is_best/order.bend as AO
import ./best_is_best/best.bend as AB

# The invariant
# -------------

def ah.nilp(rs: List<&2, ArS.Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      False{}

def ah.nonep(p: Maybe<&2, ArS.Pend>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{q}:
      False{}

def ah.I(cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>) -> Type:
  match cfg:
    case None{}:
      {Bool.and(ah.nilp(runs), ah.nonep(pend)) == True{} : Bool}
    case Some{c}:
      {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool} & {AO.ah.below(runs, seg) == True{} : Bool}

def ah.Inv(s: ArS.St) -> Type:
  match s:
    case ArS.St{cfg, +seg, mode, +runs, pend}:
      ah.I(cfg, seg, runs, pend)

# the invariant after a step's answer r on state s
def ah.IA(+s: ArS.St, r: ArS.Res) -> Type:
  ah.Inv(ArM.ar_after(r, s))

# Without a configuration
# -----------------------

def ah.ib_none_init(er: Maybe<&2, String>, harness: Bool, -c: ArS.Cfg, -fresh: Bool, -seg: Nat, -mode: ArS.Mode) -> ah.IA(ArS.St{None{}, seg, mode, Nil{}, None{}}, ArP.init.check(er, None{}, c, fresh, harness, seg, Nil{}, None{})):
  match er:
    case Some{t}:
      {==}
    case None{}:
      match harness:
        case True{}:
          ({==}, {==})
        case False{}:
          {==}

def ah.ib_none_flag(ok: Bool, -n: Nat, -seg: Nat, -mode: ArS.Mode) -> ah.IA(ArS.St{None{}, seg, mode, Nil{}, None{}}, ArP.flag.reason(ok, ArS.St{None{}, seg, mode, Nil{}, None{}}, n)):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def ah.ib_none(e: ArS.Ev, +seg: Nat, +mode: ArS.Mode) -> ah.IA(ArS.St{None{}, seg, mode, Nil{}, None{}}, ArP.step(ArS.St{None{}, seg, mode, Nil{}, None{}}, e)):
  match e:
    case ArS.Init{+c, fresh, harness}:
      ah.ib_none_init(ArP.init.err(c), harness, c, fresh, seg, mode)
    case ArS.Begin{n}:
      {==}
    case ArS.Line{t}:
      {==}
    case ArS.Finish{neg, code, timeout}:
      {==}
    case ArS.Log{st, desc, why, devs}:
      {==}
    case ArS.Flag{n, reason}:
      ah.ib_none_flag(ArL.some(reason), n, seg, mode)
    case ArS.SetMode{m}:
      {==}

# With a configuration
# --------------------

def ah.ib_same(ok: Bool, +c: ArS.Cfg, +c2: ArS.Cfg, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}, eq: {ArP.same(c, c2) == ok : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.init.keep(ok, c2, ArS.Cfg.metric(c), seg, runs, pend)):
  match ok:
    case True{}:
      +ab = ArS.abandon(ArS.Cfg.metric(c), seg, pend)
      %AO.ah.same_dir(c, c2, eq) : ({AO.ah.ord(_, ArS.snoc(runs, ab), seg) == True{} : Bool} & {AO.ah.below(ArS.snoc(runs, ab), seg) == True{} : Bool})
      (AO.ah.ord_snoc_nk(ArS.Cfg.dir(c), runs, ab, seg, ho, AO.ah.nk_ab(ArS.Cfg.metric(c), seg, pend, seg)), AO.ah.below_snoc(runs, ab, seg, hb, AO.ah.below_ab(ArS.Cfg.metric(c), seg, pend)))
    case False{}:
      (ho, hb)

def ah.ib_init(er: Maybe<&2, String>, fresh: Bool, harness: Bool, +c: ArS.Cfg, +c2: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.init.check(er, Some{c}, c2, fresh, harness, seg, runs, pend)):
  match er:
    case Some{t}:
      (ho, hb)
    case None{}:
      match fresh:
        case True{}:
          match harness:
            case True{}:
              +ab = ArS.abandon(ArS.Cfg.metric(c), seg, pend)
              +bs = AO.ah.below_snoc(runs, ab, seg, hb, AO.ah.below_ab(ArS.Cfg.metric(c), seg, pend))
              (AO.ah.nk_ord(ArS.Cfg.dir(c2), ArS.snoc(runs, ab), 1n+seg, AO.ah.below_nk(ArS.snoc(runs, ab), seg, bs)), AO.ah.below_up(ArS.snoc(runs, ab), seg, bs))
            case False{}:
              (ho, hb)
        case False{}:
          ah.ib_same(ArP.same(c, c2), c, c2, seg, mode, runs, pend, ho, hb, {==})

def ah.ib_begin(ok: Bool, +n: Nat, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.begin.at(ok, n, c, seg, mode, runs, pend)):
  match ok:
    case True{}:
      +ab = ArS.abandon(ArS.Cfg.metric(c), seg, pend)
      (AO.ah.ord_snoc_nk(ArS.Cfg.dir(c), runs, ab, seg, ho, AO.ah.nk_ab(ArS.Cfg.metric(c), seg, pend, seg)), AO.ah.below_snoc(runs, ab, seg, hb, AO.ah.below_ab(ArS.Cfg.metric(c), seg, pend)))
    case False{}:
      (ho, hb)

def ah.ib_line(m: Maybe<&2, ArL.Kv>, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArP.line.got(m, Some{c}, seg, mode, runs, id, kvs)):
  match m:
    case None{}:
      (ho, hb)
    case Some{kv}:
      match kv:
        case ArL.Kv{n, d}:
          (ho, hb)

def ah.ib_line0(pend: Maybe<&2, ArS.Pend>, +text: String, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.line(ArS.St{Some{c}, seg, mode, runs, pend}, text)):
  match pend:
    case None{}:
      (ho, hb)
    case Some{q}:
      match q:
        case ArS.Pend{+id, +kvs, fin}:
          match fin:
            case Some{p}:
              (ho, hb)
            case None{}:
              ah.ib_line(ArL.metric(text), c, seg, mode, runs, id, kvs, ho, hb)

def ah.ib_fin0(pend: Maybe<&2, ArS.Pend>, -neg: Bool, -code: Nat, -timeout: Bool, +c: ArS.Cfg, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.finish(ArS.St{Some{c}, seg, mode, runs, pend}, neg, code, timeout)):
  match pend:
    case None{}:
      (ho, hb)
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case Some{p}:
              (ho, hb)
            case None{}:
              (ho, hb)

# a logged row that keeps nothing keeps the invariant
def ah.ib_done(+c: ArS.Cfg, +seg: Nat, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String, h: {ArS.kept.st(Some{st}) == False{} : Bool}, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> {AO.ah.ord(ArS.Cfg.dir(c), ArS.snoc(runs, [ArS.row(ArS.primary(Some{c}), seg, p, Some{st}, desc)]), seg) == True{} : Bool} & {AO.ah.below(ArS.snoc(runs, [ArS.row(ArS.primary(Some{c}), seg, p, Some{st}, desc)]), seg) == True{} : Bool}:
  +r = ArS.row(ArS.primary(Some{c}), seg, p, Some{st}, desc)
  (AO.ah.ord_snoc_nk(ArS.Cfg.dir(c), runs, [r], seg, ho, AO.ah.nk_row(ArS.primary(Some{c}), seg, p, st, desc, seg, h)), AO.ah.below_snoc(runs, [r], seg, hb, AO.ah.below_row(ArS.primary(Some{c}), seg, p, Some{st}, desc)))

# a keep keeps the invariant
def ah.ib_keep(+c: ArS.Cfg, +x: ArD.Dec, +seg: Nat, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == Some{x} : Maybe<&2, ArD.Dec>}, +eqb: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == True{} : Bool}, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> {AO.ah.ord(ArS.Cfg.dir(c), ArS.snoc(runs, [ArS.row(ArS.primary(Some{c}), seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)]), seg) == True{} : Bool} & {AO.ah.below(ArS.snoc(runs, [ArS.row(ArS.primary(Some{c}), seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)]), seg) == True{} : Bool}:
  +eqm2 = Equal.trans(Maybe<&2, ArD.Dec>, ArS.lookup(kvs, ArS.primary(Some{c})), ArS.lookup(kvs, ArS.Cfg.metric(c)), Some{x}, Equal.cong(String, Maybe<&2, ArD.Dec>, k => ArS.lookup(kvs, k), ArS.primary(Some{c}), ArS.Cfg.metric(c), AH.ah.prim(c)), eqm)
  +r = ArS.row(ArS.primary(Some{c}), seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)
  (AO.ah.ord_snoc_keep(ArS.Cfg.dir(c), x, runs, r, seg, ho, eqb, AH.ah.kept_keep(id, seg, kvs, fin, desc, ArS.primary(Some{c}), x, eqm2)), AO.ah.below_snoc(runs, [r], seg, hb, AO.ah.below_row(ArS.primary(Some{c}), seg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)))

def ah.ib_why(ok: Bool, +c: ArS.Cfg, +x: ArD.Dec, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == Some{x} : Maybe<&2, ArD.Dec>}, +eqb: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == True{} : Bool}, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, ArP.keep.why(ok, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc)):
  match ok:
    case True{}:
      ah.ib_keep(c, x, seg, runs, id, kvs, fin, desc, eqm, eqb, ho, hb)
    case False{}:
      (ho, hb)

def ah.ib_beats(ok: Bool, +c: ArS.Cfg, +x: ArD.Dec, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == Some{x} : Maybe<&2, ArD.Dec>}, eqb: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == ok : Bool}, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, ArP.keep.beats(ok, x, ArS.Cfg.dir(c), why, devs, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc)):
  match ok:
    case True{}:
      ah.ib_why(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), c, x, seg, mode, runs, id, kvs, fin, desc, eqm, eqb, ho, hb)
    case False{}:
      (ho, hb)

def ah.ib_metric(m: Maybe<&2, ArD.Dec>, +c: ArS.Cfg, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, eqm: {ArS.lookup(kvs, ArS.Cfg.metric(c)) == m : Maybe<&2, ArD.Dec>}, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}, ArP.keep.metric(m, c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc)):
  match m:
    case None{}:
      (ho, hb)
    case Some{+x}:
      ah.ib_beats(ArS.beats(ArS.Cfg.dir(c), x, runs, seg), c, x, why, devs, seg, mode, runs, id, kvs, fin, desc, eqm, {==}, ho, hb)

def ah.ib_log(pend: Maybe<&2, ArS.Pend>, st: ArS.Status, +c: ArS.Cfg, +desc: String, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.log(ArS.St{Some{c}, seg, mode, runs, pend}, st, desc, why, devs)):
  match pend:
    case None{}:
      (ho, hb)
    case Some{q}:
      match q:
        case ArS.Pend{+id, +kvs, fin}:
          match fin:
            case None{}:
              (ho, hb)
            case Some{passed}:
              match passed:
                case True{}:
                  match st:
                    case ArS.Keep{}:
                      ah.ib_metric(ArS.lookup(kvs, ArS.Cfg.metric(c)), c, why, devs, seg, mode, runs, id, kvs, Some{True{}}, desc, {==}, ho, hb)
                    case ArS.Discard{}:
                      ah.ib_done(c, seg, runs, ArS.Pend{id, kvs, Some{True{}}}, ArS.Discard{}, desc, {==}, ho, hb)
                    case ArS.Crash{}:
                      (ho, hb)
                    case ArS.Checks{}:
                      ah.ib_done(c, seg, runs, ArS.Pend{id, kvs, Some{True{}}}, ArS.Checks{}, desc, {==}, ho, hb)
                case False{}:
                  match st:
                    case ArS.Keep{}:
                      (ho, hb)
                    case ArS.Discard{}:
                      ah.ib_done(c, seg, runs, ArS.Pend{id, kvs, Some{False{}}}, ArS.Discard{}, desc, {==}, ho, hb)
                    case ArS.Crash{}:
                      ah.ib_done(c, seg, runs, ArS.Pend{id, kvs, Some{False{}}}, ArS.Crash{}, desc, {==}, ho, hb)
                    case ArS.Checks{}:
                      (ho, hb)

def ah.ib_end(f: Bool, +a: List<&2, ArS.Row>, -n: Nat, +c: ArS.Cfg, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}, ho2: {AO.ah.ord(ArS.Cfg.dir(c), a, seg) == True{} : Bool}, hb2: {AO.ah.below(a, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.flag.end(f, n, Some{c}, seg, mode, a, pend)):
  match f:
    case True{}:
      (ho2, hb2)
    case False{}:
      (ho, hb)

def ah.ib_found(q: List<&2, ArS.Row> & Bool, +n: Nat, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}, ho2: {AO.ah.ord(ArS.Cfg.dir(c), AO.ah.fst(q), seg) == True{} : Bool}, hb2: {AO.ah.below(AO.ah.fst(q), seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.flag.found(q, n, Some{c}, seg, mode, pend)):
  (a, f) = q
  ah.ib_end(f, a, n, c, seg, mode, runs, pend, ho, hb, ho2, hb2)

def ah.ib_flag(ok: Bool, +n: Nat, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.flag.reason(ok, ArS.St{Some{c}, seg, mode, runs, pend}, n)):
  match ok:
    case True{}:
      ah.ib_found(ArP.flag.rows(runs, n), n, c, seg, mode, runs, pend, ho, hb, AO.ah.flag_ord(ArS.Cfg.dir(c), runs, n, seg, ho), AO.ah.flag_below(runs, n, seg, hb))
    case False{}:
      (ho, hb)

def ah.ib_some(e: ArS.Ev, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, +ho: {AO.ah.ord(ArS.Cfg.dir(c), runs, seg) == True{} : Bool}, +hb: {AO.ah.below(runs, seg) == True{} : Bool}) -> ah.IA(ArS.St{Some{c}, seg, mode, runs, pend}, ArP.step(ArS.St{Some{c}, seg, mode, runs, pend}, e)):
  match e:
    case ArS.Init{+c2, fresh, harness}:
      ah.ib_init(ArP.init.err(c2), fresh, harness, c, c2, seg, mode, runs, pend, ho, hb)
    case ArS.Begin{+n}:
      +k = {1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)) : Nat}
      ah.ib_begin(Nat.is_eq(n, k), k, c, seg, mode, runs, pend, ho, hb)
    case ArS.Line{text}:
      ah.ib_line0(pend, text, c, seg, mode, runs, ho, hb)
    case ArS.Finish{neg, code, timeout}:
      ah.ib_fin0(pend, neg, code, timeout, c, seg, mode, runs, ho, hb)
    case ArS.Log{st, desc, why, devs}:
      ah.ib_log(pend, st, c, desc, why, devs, seg, mode, runs, ho, hb)
    case ArS.Flag{+n, reason}:
      ah.ib_flag(ArL.some(reason), n, c, seg, mode, runs, pend, ho, hb)
    case ArS.SetMode{m}:
      (ho, hb)

# A step
# ------

def ah.ib0(cfg: Maybe<&2, ArS.Cfg>, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, e: ArS.Ev, +seg: Nat, +mode: ArS.Mode, inv: ah.I(cfg, seg, runs, pend)) -> ah.IA(ArS.St{cfg, seg, mode, runs, pend}, ArP.step(ArS.St{cfg, seg, mode, runs, pend}, e)):
  match cfg:
    case None{}:
      match runs:
        case Nil{}:
          match pend:
            case None{}:
              ah.ib_none(e, seg, mode)
            case Some{p}:
              AH.ah.absurd(ah.IA(ArS.St{None{}, seg, mode, Nil{}, Some{p}}, ArP.step(ArS.St{None{}, seg, mode, Nil{}, Some{p}}, e)), inv)
        case r <> t:
          AH.ah.absurd(ah.IA(ArS.St{None{}, seg, mode, r <> t, pend}, ArP.step(ArS.St{None{}, seg, mode, r <> t, pend}, e)), inv)
    case Some{+c}:
      (ho, hb) = inv
      ah.ib_some(e, c, seg, mode, runs, pend, ho, hb)

def ah.ib(s: ArS.St, e: ArS.Ev, inv: ah.Inv(s)) -> ah.IA(s, ArP.step(s, e)):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      ah.ib0(cfg, runs, pend, e, seg, mode, inv)

def ah.ib_go(evs: List<&2, ArS.Ev>, +s: ArS.St, inv: ah.Inv(s)) -> ah.Inv(ArM.ar_run.go(evs, s)):
  match evs:
    case Nil{}:
      inv
    case +e <> t:
      ah.ib_go(t, ArM.ar_after(ArP.step(s, e), s), ah.ib(s, e, inv))

# The best
# --------

def ah.ib_ok(cfg: Maybe<&2, ArS.Cfg>, runs: List<&2, ArS.Row>, +seg: Nat, -mode: ArS.Mode, -pend: Maybe<&2, ArS.Pend>, inv: ah.I(cfg, seg, runs, pend)) -> AutoresearchHistory.ar_best_ok(ArS.St{cfg, seg, mode, runs, pend}):
  match cfg:
    case None{}:
      match runs:
        case Nil{}:
          {==}
        case r <> t:
          AH.ah.absurd(AutoresearchHistory.ar_best_ok(ArS.St{None{}, seg, mode, r <> t, pend}), inv)
    case Some{+c}:
      (ho, hb) = inv
      AB.ah.best(ArS.Cfg.dir(c), runs, seg, ho)

def ah.ib_fin(s: ArS.St, inv: ah.Inv(s)) -> AutoresearchHistory.ar_best_ok(s):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      ah.ib_ok(cfg, runs, seg, mode, pend, inv)

def AutoresearchHistory.best_is_best(evs):
  ah.ib_fin(ArM.ar_run(evs), ah.ib_go(evs, ArS.St.empty(), {==}))
