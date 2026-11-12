# eukhe: the proof of LAW rows_kept: per event, the state an accepted
# step leaves (AE.ev.*): a start or an init appends the abandoned pending
# run, a log the logged one, a line, an end or the mode keeps the rows

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/events.bend as AE

def rk.R(+s: ArS.St, +s2: ArS.St) -> Type:
  &ys: List<&2, ArS.Row> -> {ArM.ar_runs(s2) == List.append(&2, ArS.Row, ArM.ar_runs(s), ys) : List<&2, ArS.Row>}

def rk.same(+s: ArS.St, +s2: ArS.St, h: AE.ev.Same(s, s2)) -> rk.R(s, s2):
  (hc, r) = h
  (hs, hr) = r
  (Nil{}, Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(s2), ArM.ar_runs(s), List.append(&2, ArS.Row, ArM.ar_runs(s), Nil{}), hr, AE.ev.app_nil(ArM.ar_runs(s))))

# the state's rows, then the abandoned pending run
def rk.gone(+s: ArS.St, +s2: ArS.St, -x: ArS.St, h: {s2 == x : ArS.St}, hr: {ArM.ar_runs(x) == ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)) : List<&2, ArS.Row>}) -> rk.R(s, s2):
  (ArM.ar_gone(s), Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(s2), ArM.ar_runs(x), List.append(&2, ArS.Row, ArM.ar_runs(s), ArM.ar_gone(s)), Equal.cong(ArS.St, List<&2, ArS.Row>, y => ArM.ar_runs(y), s2, x, h), Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(x), ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), List.append(&2, ArS.Row, ArM.ar_runs(s), ArM.ar_gone(s)), hr, AE.ev.app(ArM.ar_runs(s), ArM.ar_gone(s)))))

def rk.log(s: ArS.St, st: ArS.Status, desc: String, +s2: ArS.St, h: ArM.ar_logged(s, st, desc, s2)) -> rk.R(s, s2):
  match s:
    case ArS.St{+c, +seg, mode, +runs, pend}:
      match pend:
        case None{}:
          match h:
        case Some{+p}:
          (q1, rest) = h
          ([ArM.ar_row(c, seg, p, Some{st}, desc)], Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(s2), ArS.snoc(runs, [ArM.ar_row(c, seg, p, Some{st}, desc)]), List.append(&2, ArS.Row, runs, [ArM.ar_row(c, seg, p, Some{st}, desc)]), q1, AE.ev.app(runs, [ArM.ar_row(c, seg, p, Some{st}, desc)])))

def rk.init(+s: ArS.St, +c: ArS.Cfg, +f: Bool, +h: Bool, +s2: ArS.St, -eff: ArS.Eff, -stop: Bool, hi: AS.as.Init(ArS.Took{s2, eff, stop}, s, c, f, h)) -> rk.R(s, s2):
  (p1, r1) = hi
  (p2, r2) = r1
  (p3, r3) = r2
  rk.gone(s, s2, AS.as.InitSt(s, c, f, h), p3, {==})

def AutoresearchEvents.rows_kept(s, e, s2, eff, stop, ok, nf):
  match e:
    case ArS.Init{+c, +f, +h}:
      rk.init(s, c, f, h, s2, eff, stop, AS.as.init_took(s, c, f, h, s2, eff, stop, ok))
    case ArS.Begin{+n}:
      rk.gone(s, s2, ArS.St{ArM.ar_cfg(s), ArM.ar_seg(s), ArM.ar_mode(s), ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), Some{ArS.Pend{n, Nil{}, None{}}}}, AE.ev.begin_st(s, n, s2, eff, stop, ok), {==})
    case ArS.Line{+t}:
      rk.same(s, s2, AE.ev.after(ArP.step(s, ArS.Line{t}), y => AE.ev.Same(s, y), s2, eff, stop, ok, AE.ev.line.walk(s, t)))
    case ArS.Finish{+neg, +code, +timeout}:
      rk.same(s, s2, AE.ev.after(ArP.step(s, ArS.Finish{neg, code, timeout}), y => AE.ev.Same(s, y), s2, eff, stop, ok, AE.ev.finish.walk(s, neg, code, timeout)))
    case ArS.Log{+st, +d, +w, +v}:
      rk.log(s, st, d, s2, AE.ev.logged(s, st, d, w, v, s2, eff, stop, ok))
    case ArS.Flag{n, r}:
      AS.as.absurd_tf(rk.R(s, s2), nf)
    case ArS.SetMode{+m}:
      rk.same(s, s2, AE.ev.after(ArP.step(s, ArS.SetMode{m}), y => AE.ev.Same(s, y), s2, eff, stop, ok, AE.ev.mode.walk(s, m)))
