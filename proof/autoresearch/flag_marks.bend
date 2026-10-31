# eukhe: the proof of LAW flag_marks

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

# a found flag: the run n was logged and is flagged in the rows q
def fmk.Mark(q: List<&2, ArS.Row> & Bool, runs: List<&2, ArS.Row>, +n: Nat) -> Type:
  (rs, f) = q
  {f == True{} : Bool} -> {Bool.and(Autoresearch.ar_logged_id(runs, n), Autoresearch.ar_flagged(rs, n)) == True{} : Bool}

def fmk.hit2(a: Bool, h: Bool, -b: Bool, -c: Bool, eh: {Bool.and(a, h) == True{} : Bool}) -> {Bool.and(Bool.or(Bool.and(a, h), b), Bool.or(Bool.and(a, True{}), c)) == True{} : Bool}:
  match a:
    case True{}:
      match h:
        case True{}:
          {==}
        case False{}:
          AS.as.absurd({Bool.and(Bool.or(False{}, b), Bool.or(True{}, c)) == True{} : Bool}, eh)
    case False{}:
      AS.as.absurd({Bool.and(Bool.or(False{}, b), Bool.or(False{}, c)) == True{} : Bool}, eh)

def fmk.hit(r: ArS.Row, +n: Nat, -b: Bool, -c: Bool, eh: {ArP.flag.hit(r, n) == True{} : Bool}) -> {Bool.and(Bool.or(Autoresearch.ar_logged_id.at(r, n), b), Bool.or(Autoresearch.ar_flagged.at(ArP.flag.set(r), n), c)) == True{} : Bool}:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      fmk.hit2(Nat.is_eq(i, n), ArS.has(st), b, c, eh)

def fmk.both(a: Bool, b: Bool, c: Bool, d: Bool, e: {Bool.and(b, d) == True{} : Bool}) -> {Bool.and(Bool.or(a, b), Bool.or(c, d)) == True{} : Bool}:
  match a b c d:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      AS.as.absurd({False{} == True{} : Bool}, e)
    case True{} False{} c d:
      AS.as.absurd({Bool.and(True{}, Bool.or(c, d)) == True{} : Bool}, e)
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      AS.as.absurd({False{} == True{} : Bool}, e)
    case False{} False{} c d:
      AS.as.absurd({False{} == True{} : Bool}, e)

def fmk.miss(q: List<&2, ArS.Row> & Bool, +r: ArS.Row, +t: List<&2, ArS.Row>, +n: Nat, hq: fmk.Mark(q, t, n)) -> fmk.Mark(ArP.flag.at(False{}, r, t, q), r <> t, n):
  (rs, found) = q
  f => fmk.both(Autoresearch.ar_logged_id.at(r, n), Autoresearch.ar_logged_id(t, n), Autoresearch.ar_flagged.at(r, n), Autoresearch.ar_flagged(rs, n), hq(f))

def fmk.at(hit: Bool, +r: ArS.Row, +t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, +n: Nat, hq: fmk.Mark(q, t, n), eh: {ArP.flag.hit(r, n) == hit : Bool}) -> fmk.Mark(ArP.flag.at(hit, r, t, q), r <> t, n):
  match hit:
    case True{}:
      f => fmk.hit(r, n, Autoresearch.ar_logged_id(t, n), Autoresearch.ar_flagged(t, n), eh)
    case False{}:
      fmk.miss(q, r, t, n, hq)

def fmk.rows(runs: List<&2, ArS.Row>, +n: Nat) -> fmk.Mark(ArP.flag.rows(runs, n), runs, n):
  match runs:
    case Nil{}:
      f => AS.as.absurd({False{} == True{} : Bool}, f)
    case +r <> +t:
      fmk.at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), n, fmk.rows(t, n), {==})

# what an accepted flag leaves
def fmk.P(r: ArS.Res, s: ArS.St, +n: Nat, reason: String) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {Bool.and(SL.nonempty(reason), Bool.and(Autoresearch.ar_logged_id(Autoresearch.ar_runs(s), n), Autoresearch.ar_flagged(Autoresearch.ar_runs(s2), n))) == True{} : Bool}
    case ArS.Refuse{t}:
      Unit

def fmk.found(q: List<&2, ArS.Row> & Bool, +n: Nat, -cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, -h: Char, -t: String, hq: fmk.Mark(q, runs, n))
  -> fmk.P(ArP.flag.found(q, n, cfg, seg, mode, pend), ArS.St{cfg, seg, mode, runs, pend}, n, SCon{h, t}):
  (rs, found) = q
  match found:
    case True{}:
      hq({==})
    case False{}:
      Unit{}

def fmk.walk(s: ArS.St, +n: Nat, reason: String) -> fmk.P(ArP.step(s, ArS.Flag{n, reason}), s, n, reason):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, +pend}:
      match reason:
        case SNil{}:
          Unit{}
        case SCon{h, t}:
          fmk.found(ArP.flag.rows(runs, n), n, cfg, seg, mode, runs, pend, h, t, fmk.rows(runs, n))

def Autoresearch.flag_marks(s, n, reason, s2, eff, stop, ok):
  %ok : fmk.P(_, s, n, reason)
  fmk.walk(s, n, reason)
