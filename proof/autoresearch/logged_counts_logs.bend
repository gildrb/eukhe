# eukhe: the proof of LAW logged_counts_logs: after any history no row is
# of a later segment (the invariant of best_is_best, PBB.ah.Inv). Per
# event, the state an accepted step leaves (AE.ev.*): a start or an init
# appends an abandoned row, which has no status; a log appends one logged
# row of the segment; a flag keeps every row's segment and status; a new
# segment counts no earlier row

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ./base/step.bend as AS
import ./base/history.bend as AH
import ./base/events.bend as AE
import ./best_is_best/order.bend as AO
import ./best_is_best.bend as PBB

# Counts
# ------

def lcl.st(s: ArS.St) -> {ArS.St.logged(s) == ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)) : Nat}:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      {==}

def lcl.snoc(rs: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat) -> {ArS.logged(ArS.snoc(rs, ys), seg) == Nat.add(ArS.logged(rs, seg), ArS.logged(ys, seg)) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      Equal.trans(Nat, Nat.add(ArS.logged.at(r, seg), ArS.logged(ArS.snoc(t, ys), seg)), Nat.add(ArS.logged.at(r, seg), Nat.add(ArS.logged(t, seg), ArS.logged(ys, seg))), Nat.add(Nat.add(ArS.logged.at(r, seg), ArS.logged(t, seg)), ArS.logged(ys, seg)), Equal.cong(Nat, Nat, y => Nat.add(ArS.logged.at(r, seg), y), ArS.logged(ArS.snoc(t, ys), seg), Nat.add(ArS.logged(t, seg), ArS.logged(ys, seg)), lcl.snoc(t, ys, seg)), Equal.sym(Nat, Nat.add(Nat.add(ArS.logged.at(r, seg), ArS.logged(t, seg)), ArS.logged(ys, seg)), Nat.add(ArS.logged.at(r, seg), Nat.add(ArS.logged(t, seg), ArS.logged(ys, seg))), AH.ah.add_assoc(ArS.logged.at(r, seg), ArS.logged(t, seg), ArS.logged(ys, seg))))

# an abandoned row has no status: it is never counted
def lcl.gone(s: ArS.St, +seg: Nat) -> {ArS.logged(ArM.ar_gone(s), seg) == 0n : Nat}:
  match s:
    case ArS.St{c, sg, mode, runs, pend}:
      match pend:
        case None{}:
          {==}
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              %Equal.sym(Bool, Bool.and(Nat.is_eq(sg, seg), False{}), False{}, AE.ev.and_false(Nat.is_eq(sg, seg))) : {Nat.add(ArS.one(_), 0n) == 0n : Nat}
              {==}

# the rows, then the abandoned pending run, counted in segment g
def lcl.ab(+s: ArS.St, +g: Nat) -> {ArS.logged(ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), g) == ArS.logged(ArM.ar_runs(s), g) : Nat}:
  Equal.trans(Nat, ArS.logged(ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), g), Nat.add(ArS.logged(ArM.ar_runs(s), g), ArS.logged(ArM.ar_gone(s), g)), ArS.logged(ArM.ar_runs(s), g), lcl.snoc(ArM.ar_runs(s), ArM.ar_gone(s), g), Equal.trans(Nat, Nat.add(ArS.logged(ArM.ar_runs(s), g), ArS.logged(ArM.ar_gone(s), g)), Nat.add(ArS.logged(ArM.ar_runs(s), g), 0n), ArS.logged(ArM.ar_runs(s), g), Equal.cong(Nat, Nat, y => Nat.add(ArS.logged(ArM.ar_runs(s), g), y), ArS.logged(ArM.ar_gone(s), g), 0n, lcl.gone(s, g)), AH.ah.add_zero(ArS.logged(ArM.ar_runs(s), g))))

# no row of a later segment: none counted in the next one
def lcl.next(rs: List<&2, ArS.Row>, +seg: Nat, +hb: {AO.ah.below(rs, seg) == True{} : Bool}) -> {ArS.logged(rs, 1n+seg) == 0n : Nat}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{i, +sg, st, m, ms, ps, fn, fl, desc} <> +t:
      +h1 = AH.ah.and_l(Nat.is_le(sg, seg), AO.ah.below(t, seg), hb)
      +h2 = AH.ah.and_r(Nat.is_le(sg, seg), AO.ah.below(t, seg), hb)
      %Equal.sym(Bool, Nat.is_eq(sg, 1n+seg), False{}, AO.ah.le_ne(sg, seg, h1)) : {Nat.add(ArS.one(Bool.and(_, ArS.has(st))), ArS.logged(t, 1n+seg)) == 0n : Nat}
      lcl.next(t, seg, h2)

# a flag keeps every row's segment and status
def lcl.flag_at(hit: Bool, r: ArS.Row, -t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, +seg: Nat, hq: {ArS.logged(AE.ev.fst(q), seg) == ArS.logged(t, seg) : Nat}) -> {ArS.logged(AE.ev.fst(ArP.flag.at(hit, r, t, q)), seg) == ArS.logged(r <> t, seg) : Nat}:
  match hit:
    case True{}:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          {==}
    case False{}:
      match q:
        case (a, f):
          Equal.cong(Nat, Nat, y => Nat.add(ArS.logged.at(r, seg), y), ArS.logged(a, seg), ArS.logged(t, seg), hq)

def lcl.flag(rs: List<&2, ArS.Row>, +n: Nat, +seg: Nat) -> {ArS.logged(AE.ev.fst(ArP.flag.rows(rs, n)), seg) == ArS.logged(rs, seg) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      lcl.flag_at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), seg, lcl.flag(t, n, seg))

# The steps
# ---------

def lcl.G(+s: ArS.St, e: ArS.Ev, s2: ArS.St) -> Type:
  {ArS.St.logged(s2) == AutoresearchHistory.ar_logged_next(s, e) : Nat}

# a state whose rows are those of s, then the abandoned run, in the segment
def lcl.abst(+s: ArS.St, e: ArS.Ev, +s2: ArS.St, -x: ArS.St, h: {s2 == x : ArS.St}, hx: {ArS.St.logged(x) == ArS.logged(ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), ArM.ar_seg(s)) : Nat}, hn: {AutoresearchHistory.ar_logged_next(s, e) == ArS.St.logged(s) : Nat}) -> lcl.G(s, e, s2):
  Equal.trans(Nat, ArS.St.logged(s2), ArS.St.logged(x), AutoresearchHistory.ar_logged_next(s, e), Equal.cong(ArS.St, Nat, y => ArS.St.logged(y), s2, x, h), Equal.trans(Nat, ArS.St.logged(x), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), AutoresearchHistory.ar_logged_next(s, e), Equal.trans(Nat, ArS.St.logged(x), ArS.logged(ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), ArM.ar_seg(s)), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), hx, lcl.ab(s, ArM.ar_seg(s))), Equal.trans(Nat, ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), ArS.St.logged(s), AutoresearchHistory.ar_logged_next(s, e), Equal.sym(Nat, ArS.St.logged(s), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), lcl.st(s)), Equal.sym(Nat, AutoresearchHistory.ar_logged_next(s, e), ArS.St.logged(s), hn))))

# a line, an end or the mode: same segment and rows
def lcl.same(+s: ArS.St, e: ArS.Ev, +s2: ArS.St, h: AE.ev.Same(s, s2), hn: {AutoresearchHistory.ar_logged_next(s, e) == ArS.St.logged(s) : Nat}) -> lcl.G(s, e, s2):
  (hc, r) = h
  (hs, hr) = r
  +e1 = Equal.cong(List<&2, ArS.Row>, Nat, y => ArS.logged(y, ArM.ar_seg(s2)), ArM.ar_runs(s2), ArM.ar_runs(s), hr)
  +e2 = Equal.cong(Nat, Nat, g => ArS.logged(ArM.ar_runs(s), g), ArM.ar_seg(s2), ArM.ar_seg(s), hs)
  Equal.trans(Nat, ArS.St.logged(s2), ArS.logged(ArM.ar_runs(s2), ArM.ar_seg(s2)), AutoresearchHistory.ar_logged_next(s, e), lcl.st(s2), Equal.trans(Nat, ArS.logged(ArM.ar_runs(s2), ArM.ar_seg(s2)), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s2)), AutoresearchHistory.ar_logged_next(s, e), e1, Equal.trans(Nat, ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s2)), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), AutoresearchHistory.ar_logged_next(s, e), e2, Equal.trans(Nat, ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), ArS.St.logged(s), AutoresearchHistory.ar_logged_next(s, e), Equal.sym(Nat, ArS.St.logged(s), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), lcl.st(s)), Equal.sym(Nat, AutoresearchHistory.ar_logged_next(s, e), ArS.St.logged(s), hn)))))

# Init: per segment flag and experiment
def lcl.init_st(+c: ArS.Cfg, f: Bool, +h: Bool, cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, inv: PBB.ah.I(cfg, seg, runs, pend)) -> {ArS.St.logged(AS.as.InitSt(ArS.St{cfg, seg, mode, runs, pend}, c, f, h)) == AutoresearchHistory.ar_logged_next(ArS.St{cfg, seg, mode, runs, pend}, ArS.Init{c, f, h}) : Nat}:
  match f:
    case False{}:
      %Equal.sym(Nat, Nat.add(seg, 0n), seg, AS.as.add_zero(seg)) : {ArS.logged(ArS.snoc(runs, ArM.ar_gone(ArS.St{cfg, seg, mode, runs, pend})), _) == ArS.logged(runs, seg) : Nat}
      lcl.ab(ArS.St{cfg, seg, mode, runs, pend}, seg)
    case True{}:
      match cfg:
        case None{}:
          %Equal.sym(Nat, Nat.add(seg, 0n), seg, AS.as.add_zero(seg)) : {ArS.logged(ArS.snoc(runs, ArM.ar_gone(ArS.St{None{}, seg, mode, runs, pend})), _) == ArS.logged(runs, seg) : Nat}
          lcl.ab(ArS.St{None{}, seg, mode, runs, pend}, seg)
        case Some{o}:
          (ho, hb) = inv
          %Equal.sym(Nat, Nat.add(seg, 1n), 1n+seg, AS.as.add_one(seg)) : {ArS.logged(ArS.snoc(runs, ArM.ar_gone(ArS.St{Some{o}, seg, mode, runs, pend})), _) == 0n : Nat}
          Equal.trans(Nat, ArS.logged(ArS.snoc(runs, ArM.ar_gone(ArS.St{Some{o}, seg, mode, runs, pend})), 1n+seg), ArS.logged(runs, 1n+seg), 0n, lcl.ab(ArS.St{Some{o}, seg, mode, runs, pend}, 1n+seg), lcl.next(runs, seg, hb))

def lcl.init_s(+c: ArS.Cfg, f: Bool, +h: Bool, s: ArS.St, inv: PBB.ah.Inv(s)) -> {ArS.St.logged(AS.as.InitSt(s, c, f, h)) == AutoresearchHistory.ar_logged_next(s, ArS.Init{c, f, h}) : Nat}:
  match s:
    case ArS.St{cfg, +seg, +mode, +runs, +pend}:
      lcl.init_st(c, f, h, cfg, seg, mode, runs, pend, inv)

def lcl.init(+c: ArS.Cfg, +f: Bool, +h: Bool, +s: ArS.St, +s2: ArS.St, -eff: ArS.Eff, -stop: Bool, hi: AS.as.Init(ArS.Took{s2, eff, stop}, s, c, f, h), inv: PBB.ah.Inv(s)) -> lcl.G(s, ArS.Init{c, f, h}, s2):
  (p1, r1) = hi
  (p2, r2) = r1
  (p3, r3) = r2
  Equal.trans(Nat, ArS.St.logged(s2), ArS.St.logged(AS.as.InitSt(s, c, f, h)), AutoresearchHistory.ar_logged_next(s, ArS.Init{c, f, h}), Equal.cong(ArS.St, Nat, y => ArS.St.logged(y), s2, AS.as.InitSt(s, c, f, h), p3), lcl.init_s(c, f, h, s, inv))

# Log: one logged row of the segment
def lcl.log(s: ArS.St, +st: ArS.Status, +d: String, -w: Maybe<&2, String>, -v: Nat, +s2: ArS.St, hl: ArM.ar_logged(s, st, d, s2)) -> lcl.G(s, ArS.Log{st, d, w, v}, s2):
  match s:
    case ArS.St{+c, +seg, mode, +runs, pend}:
      match pend:
        case None{}:
          match hl:
        case Some{p}:
          match p:
            case ArS.Pend{+id, +kvs, +fin}:
              (q1, rest) = hl
              (q2, rest2) = rest
              (q3, q4) = rest2
              +row = ArM.ar_row(c, seg, ArS.Pend{id, kvs, fin}, Some{st}, d)
              +e1 = Equal.cong(List<&2, ArS.Row>, Nat, y => ArS.logged(y, ArM.ar_seg(s2)), ArM.ar_runs(s2), ArS.snoc(runs, [row]), q1)
              +e2 = Equal.cong(Nat, Nat, g => ArS.logged(ArS.snoc(runs, [row]), g), ArM.ar_seg(s2), seg, q4)
              +e3 = lcl.snoc(runs, [row], seg)
              +e4 = Equal.cong(Bool, Nat, b => Nat.add(ArS.logged(runs, seg), Nat.add(ArS.one(Bool.and(b, True{})), 0n)), Nat.is_eq(seg, seg), True{}, AH.ah.eq_refl(seg))
              +e5 = AS.as.add_one(ArS.logged(runs, seg))
              Equal.trans(Nat, ArS.St.logged(s2), ArS.logged(ArM.ar_runs(s2), ArM.ar_seg(s2)), 1n+ArS.logged(runs, seg), lcl.st(s2), Equal.trans(Nat, ArS.logged(ArM.ar_runs(s2), ArM.ar_seg(s2)), ArS.logged(ArS.snoc(runs, [row]), ArM.ar_seg(s2)), 1n+ArS.logged(runs, seg), e1, Equal.trans(Nat, ArS.logged(ArS.snoc(runs, [row]), ArM.ar_seg(s2)), ArS.logged(ArS.snoc(runs, [row]), seg), 1n+ArS.logged(runs, seg), e2, Equal.trans(Nat, ArS.logged(ArS.snoc(runs, [row]), seg), Nat.add(ArS.logged(runs, seg), ArS.logged([row], seg)), 1n+ArS.logged(runs, seg), e3, Equal.trans(Nat, Nat.add(ArS.logged(runs, seg), ArS.logged([row], seg)), Nat.add(ArS.logged(runs, seg), 1n), 1n+ArS.logged(runs, seg), e4, e5)))))

# Flag: rows walked, segments and statuses kept
def lcl.flag_st(+s: ArS.St, +n: Nat, -r: String, +s2: ArS.St, h: AE.ev.FlagSt(s, n, s2)) -> lcl.G(s, ArS.Flag{n, r}, s2):
  +x = {ArS.St{ArM.ar_cfg(s), ArM.ar_seg(s), ArM.ar_mode(s), AE.ev.fst(ArP.flag.rows(ArM.ar_runs(s), n)), ArM.ar_pend(s)} : ArS.St}
  Equal.trans(Nat, ArS.St.logged(s2), ArS.St.logged(x), ArS.St.logged(s), Equal.cong(ArS.St, Nat, y => ArS.St.logged(y), s2, x, h), Equal.trans(Nat, ArS.St.logged(x), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), ArS.St.logged(s), lcl.flag(ArM.ar_runs(s), n, ArM.ar_seg(s)), Equal.sym(Nat, ArS.St.logged(s), ArS.logged(ArM.ar_runs(s), ArM.ar_seg(s)), lcl.st(s))))

def lcl.step(+s: ArS.St, e: ArS.Ev, +s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}, inv: PBB.ah.Inv(s)) -> lcl.G(s, e, s2):
  match e:
    case ArS.Init{+c, +f, +h}:
      lcl.init(c, f, h, s, s2, eff, stop, AS.as.init_took(s, c, f, h, s2, eff, stop, ok), inv)
    case ArS.Begin{+n}:
      lcl.abst(s, ArS.Begin{n}, s2, ArS.St{ArM.ar_cfg(s), ArM.ar_seg(s), ArM.ar_mode(s), ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), Some{ArS.Pend{n, Nil{}, None{}}}}, AE.ev.begin_st(s, n, s2, eff, stop, ok), {==}, {==})
    case ArS.Line{+t}:
      lcl.same(s, ArS.Line{t}, s2, AE.ev.after(ArP.step(s, ArS.Line{t}), y => AE.ev.Same(s, y), s2, eff, stop, ok, AE.ev.line.walk(s, t)), {==})
    case ArS.Finish{+neg, +code, +timeout}:
      lcl.same(s, ArS.Finish{neg, code, timeout}, s2, AE.ev.after(ArP.step(s, ArS.Finish{neg, code, timeout}), y => AE.ev.Same(s, y), s2, eff, stop, ok, AE.ev.finish.walk(s, neg, code, timeout)), {==})
    case ArS.Log{+st, +d, +w, +v}:
      lcl.log(s, st, d, w, v, s2, AE.ev.logged(s, st, d, w, v, s2, eff, stop, ok))
    case ArS.Flag{+n, +r}:
      lcl.flag_st(s, n, r, s2, AE.ev.after(ArP.step(s, ArS.Flag{n, r}), y => AE.ev.FlagSt(s, n, y), s2, eff, stop, ok, AE.ev.flag.walk(s, n, r)))
    case ArS.SetMode{+m}:
      lcl.same(s, ArS.SetMode{m}, s2, AE.ev.after(ArP.step(s, ArS.SetMode{m}), y => AE.ev.Same(s, y), s2, eff, stop, ok, AE.ev.mode.walk(s, m)), {==})

def AutoresearchHistory.logged_counts_logs(evs, e, s2, eff, stop, ok):
  lcl.step(ArM.ar_run(evs), e, s2, eff, stop, ok, PBB.ah.ib_go(evs, ArS.St.empty(), {==}))
