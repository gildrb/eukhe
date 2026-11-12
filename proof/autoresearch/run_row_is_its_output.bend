# eukhe: the proof of LAW run_row_is_its_output: the start leaves run n
# pending with no metrics (AE.ev.begin_st); each output line puts its
# METRIC into the pending run (rr.lines); the end, if any, sets its
# verdict; the log, start or init that ends it appends its row (rr.ends).
# The row's metrics are then read against the lines: the code's put keeps
# one value per name, the last (rr.bput_*, rr.value)

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/events.bend as AE
import ./metric_last_wins.bend as PArMetricLastWins

# Terms
# -----

# the pending run's metrics after a line read as m
def rr.kput(kvs: List<&2, ArL.Kv>, m: Maybe<&2, ArL.Kv>) -> List<&2, ArL.Kv>:
  match m:
    case None{}:
      kvs
    case Some{ArL.Kv{k, d}}:
      ArS.put(kvs, k, d)

# its metrics after the lines ts
def rr.lk.go(ts: List<&2, String>, kvs: List<&2, ArL.Kv>) -> List<&2, ArL.Kv>:
  match ts:
    case Nil{}:
      kvs
    case t <> r:
      rr.lk.go(r, rr.kput(kvs, ArL.metric(t)))

def rr.lk(kvs: List<&2, ArL.Kv>, ts: List<&2, String>) -> List<&2, ArL.Kv>:
  rr.lk.go(ts, kvs)

# the values bs with the first one set to d (d alone when there is none)
def rr.rfirst(bs: List<&2, ArD.Dec>, d: ArD.Dec) -> List<&2, ArD.Dec>:
  match bs:
    case Nil{}:
      [d]
    case v <> r:
      d <> r

def rr.bhit(hit: Bool, d: ArD.Dec, acc: List<&2, ArD.Dec>) -> List<&2, ArD.Dec>:
  match hit:
    case True{}:
      rr.rfirst(acc, d)
    case False{}:
      acc

def rr.bstep(m: Maybe<&2, ArL.Kv>, +x: String, acc: List<&2, ArD.Dec>) -> List<&2, ArD.Dec>:
  match m:
    case None{}:
      acc
    case Some{ArL.Kv{k, d}}:
      rr.bhit(String.eq(k, x), d, acc)

# the values of name x after the lines ts, from acc
def rr.B(ts: List<&2, String>, +x: String, acc: List<&2, ArD.Dec>) -> List<&2, ArD.Dec>:
  match ts:
    case Nil{}:
      acc
    case t <> r:
      rr.B(r, x, rr.bstep(ArL.metric(t), x, acc))

# the rows after the start, and the state with run n pending
def rr.R0(+s: ArS.St) -> List<&2, ArS.Row>:
  ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s))

def rr.S(+s: ArS.St, n: Nat, kvs: List<&2, ArL.Kv>, f: Maybe<&2, Bool>) -> ArS.St:
  ArS.St{ArM.ar_cfg(s), ArM.ar_seg(s), ArM.ar_mode(s), rr.R0(s), Some{ArS.Pend{n, kvs, f}}}

# the law's conclusion
def rr.Goal(+s: ArS.St, +n: Nat, +ts: List<&2, String>, +mid: List<&2, ArS.Ev>, +e: ArS.Ev, +s2: ArS.St) -> Type:
  &r: ArS.Row -> {ArM.ar_runs(s2) == List.append(&2, ArS.Row, ArM.ar_runs(ArM.ar_after(ArP.step(s, ArS.Begin{n}), s)), [r]) : List<&2, ArS.Row>} & AutoresearchEvents.ar_row_is(r, n, ArM.ar_seg(s), AutoresearchEvents.ar_status_of(e), AutoresearchEvents.ar_mid_passed(mid), AutoresearchEvents.ar_mid_finished(mid), AutoresearchEvents.ar_desc_of(e), ArM.ar_name(ArM.ar_cfg(s)), ts)

# Strings
# -------

# k is n and n is x, so String.eq(k, n) holds: it cannot be False
def rr.kx.at(c: Bool, +k: String, +n: String, +x: String, hc: {String.eq(k, x) == c : Bool}, hb: {String.eq(k, n) == False{} : Bool}, h: {String.eq(n, x) == True{} : Bool}) -> {String.eq(k, x) == False{} : Bool}:
  match c:
    case True{}:
      +ek = AS.as.str_eq(k, x, hc)
      +en = AS.as.str_eq(n, x, h)
      +exx = Equal.trans(Bool, String.eq(x, x), String.eq(k, x), String.eq(k, n),
        Equal.cong(String, Bool, y => String.eq(y, x), x, k, Equal.sym(String, k, x, ek)),
        Equal.cong(String, Bool, y => String.eq(k, y), x, n, Equal.sym(String, n, x, en)))
      AS.as.absurd_tf({String.eq(k, x) == False{} : Bool}, Equal.trans(Bool, True{}, String.eq(x, x), False{}, Equal.sym(Bool, String.eq(x, x), True{}, AS.as.str_refl(x)), Equal.trans(Bool, String.eq(x, x), String.eq(k, n), False{}, exx, hb)))
    case False{}:
      hc

# Values of one name
# ------------------

# put of another name keeps the values of x
def rr.bput_ne.at(b: Bool, +k: String, -v: ArD.Dec, +t: List<&2, ArL.Kv>, +n: String, -d: ArD.Dec, +x: String, hb: {String.eq(k, n) == b : Bool}, h: {String.eq(n, x) == False{} : Bool}, ih: {AutoresearchEvents.ar_binds(ArS.put(t, n, d), x) == AutoresearchEvents.ar_binds(t, x) : List<&2, ArD.Dec>}) -> {AutoresearchEvents.ar_binds(ArS.put.at(b, k, v, t, n, d, ArS.put(t, n, d)), x) == AutoresearchEvents.ar_binds.at(String.eq(k, x), v, AutoresearchEvents.ar_binds(t, x)) : List<&2, ArD.Dec>}:
  match b:
    case True{}:
      +B = AutoresearchEvents.ar_binds(t, x)
      %Equal.sym(String, k, n, AS.as.str_eq(k, n, hb)) : {AutoresearchEvents.ar_binds.at(String.eq(n, x), d, B) == AutoresearchEvents.ar_binds.at(String.eq(_, x), v, B) : List<&2, ArD.Dec>}
      %Equal.sym(Bool, String.eq(n, x), False{}, h) : {AutoresearchEvents.ar_binds.at(_, d, B) == AutoresearchEvents.ar_binds.at(_, v, B) : List<&2, ArD.Dec>}
      {==}
    case False{}:
      Equal.cong(List<&2, ArD.Dec>, List<&2, ArD.Dec>, l => AutoresearchEvents.ar_binds.at(String.eq(k, x), v, l), AutoresearchEvents.ar_binds(ArS.put(t, n, d), x), AutoresearchEvents.ar_binds(t, x), ih)

def rr.bput_ne(kvs: List<&2, ArL.Kv>, +n: String, +d: ArD.Dec, +x: String, +h: {String.eq(n, x) == False{} : Bool}) -> {AutoresearchEvents.ar_binds(ArS.put(kvs, n, d), x) == AutoresearchEvents.ar_binds(kvs, x) : List<&2, ArD.Dec>}:
  match kvs:
    case Nil{}:
      %Equal.sym(Bool, String.eq(n, x), False{}, h) : {AutoresearchEvents.ar_binds.at(_, d, Nil{}) == Nil{} : List<&2, ArD.Dec>}
      {==}
    case ArL.Kv{+k, v} <> +t:
      rr.bput_ne.at(String.eq(k, n), k, v, t, n, d, x, {==}, h, rr.bput_ne(t, n, d, x, h))

# put of name x sets the first value of x, or adds it
def rr.bput_eq.at(b: Bool, +k: String, -v: ArD.Dec, +t: List<&2, ArL.Kv>, +n: String, +d: ArD.Dec, +x: String, hb: {String.eq(k, n) == b : Bool}, h: {String.eq(n, x) == True{} : Bool}, ih: {AutoresearchEvents.ar_binds(ArS.put(t, n, d), x) == rr.rfirst(AutoresearchEvents.ar_binds(t, x), d) : List<&2, ArD.Dec>}) -> {AutoresearchEvents.ar_binds(ArS.put.at(b, k, v, t, n, d, ArS.put(t, n, d)), x) == rr.rfirst(AutoresearchEvents.ar_binds.at(String.eq(k, x), v, AutoresearchEvents.ar_binds(t, x)), d) : List<&2, ArD.Dec>}:
  match b:
    case True{}:
      +B = AutoresearchEvents.ar_binds(t, x)
      %Equal.sym(String, k, n, AS.as.str_eq(k, n, hb)) : {AutoresearchEvents.ar_binds.at(String.eq(n, x), d, B) == rr.rfirst(AutoresearchEvents.ar_binds.at(String.eq(_, x), v, B), d) : List<&2, ArD.Dec>}
      %Equal.sym(Bool, String.eq(n, x), True{}, h) : {AutoresearchEvents.ar_binds.at(_, d, B) == rr.rfirst(AutoresearchEvents.ar_binds.at(_, v, B), d) : List<&2, ArD.Dec>}
      {==}
    case False{}:
      +kx = rr.kx.at(String.eq(k, x), k, n, x, {==}, hb, h)
      %Equal.sym(Bool, String.eq(k, x), False{}, kx) : {AutoresearchEvents.ar_binds.at(_, v, AutoresearchEvents.ar_binds(ArS.put(t, n, d), x)) == rr.rfirst(AutoresearchEvents.ar_binds.at(_, v, AutoresearchEvents.ar_binds(t, x)), d) : List<&2, ArD.Dec>}
      ih

def rr.bput_eq(kvs: List<&2, ArL.Kv>, +n: String, +d: ArD.Dec, +x: String, +h: {String.eq(n, x) == True{} : Bool}) -> {AutoresearchEvents.ar_binds(ArS.put(kvs, n, d), x) == rr.rfirst(AutoresearchEvents.ar_binds(kvs, x), d) : List<&2, ArD.Dec>}:
  match kvs:
    case Nil{}:
      %Equal.sym(Bool, String.eq(n, x), True{}, h) : {AutoresearchEvents.ar_binds.at(_, d, Nil{}) == [d] : List<&2, ArD.Dec>}
      {==}
    case ArL.Kv{+k, v} <> +t:
      rr.bput_eq.at(String.eq(k, n), k, v, t, n, d, x, {==}, h, rr.bput_eq(t, n, d, x, h))

def rr.bkput.at(b: Bool, +kvs: List<&2, ArL.Kv>, +k: String, +d: ArD.Dec, +x: String, hb: {String.eq(k, x) == b : Bool}) -> {AutoresearchEvents.ar_binds(ArS.put(kvs, k, d), x) == rr.bhit(b, d, AutoresearchEvents.ar_binds(kvs, x)) : List<&2, ArD.Dec>}:
  match b:
    case True{}:
      rr.bput_eq(kvs, k, d, x, hb)
    case False{}:
      rr.bput_ne(kvs, k, d, x, hb)

def rr.bkput(m: Maybe<&2, ArL.Kv>, +kvs: List<&2, ArL.Kv>, +x: String) -> {AutoresearchEvents.ar_binds(rr.kput(kvs, m), x) == rr.bstep(m, x, AutoresearchEvents.ar_binds(kvs, x)) : List<&2, ArD.Dec>}:
  match m:
    case None{}:
      {==}
    case Some{kv}:
      match kv:
        case ArL.Kv{+k, +d}:
          rr.bkput.at(String.eq(k, x), kvs, k, d, x, {==})

# the values of x after the lines are those the fold reads
def rr.bfold(ts: List<&2, String>, +kvs: List<&2, ArL.Kv>, +x: String) -> {AutoresearchEvents.ar_binds(rr.lk(kvs, ts), x) == rr.B(ts, x, AutoresearchEvents.ar_binds(kvs, x)) : List<&2, ArD.Dec>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> r:
      +k2 = rr.kput(kvs, ArL.metric(t))
      Equal.trans(List<&2, ArD.Dec>, AutoresearchEvents.ar_binds(rr.lk(k2, r), x), rr.B(r, x, AutoresearchEvents.ar_binds(k2, x)), rr.B(r, x, rr.bstep(ArL.metric(t), x, AutoresearchEvents.ar_binds(kvs, x))),
        rr.bfold(r, k2, x),
        Equal.cong(List<&2, ArD.Dec>, List<&2, ArD.Dec>, c => rr.B(r, x, c), AutoresearchEvents.ar_binds(k2, x), rr.bstep(ArL.metric(t), x, AutoresearchEvents.ar_binds(kvs, x)), rr.bkput(ArL.metric(t), kvs, x)))

def rr.bm1.at(b: Bool, -d: ArD.Dec, a: Maybe<&2, ArD.Dec>) -> {rr.bhit(b, d, AutoresearchEvents.ar_mlist(a)) == AutoresearchEvents.ar_mlist(AutoresearchEvents.ar_value_hit(b, d, a)) : List<&2, ArD.Dec>}:
  match b:
    case True{}:
      match a:
        case None{}:
          {==}
        case Some{y}:
          {==}
    case False{}:
      {==}

def rr.bm1(m: Maybe<&2, ArL.Kv>, +x: String, a: Maybe<&2, ArD.Dec>) -> {rr.bstep(m, x, AutoresearchEvents.ar_mlist(a)) == AutoresearchEvents.ar_mlist(AutoresearchEvents.ar_value_at(m, x, a)) : List<&2, ArD.Dec>}:
  match m:
    case None{}:
      {==}
    case Some{kv}:
      match kv:
        case ArL.Kv{+k, d}:
          rr.bm1.at(String.eq(k, x), d, a)

# from at most one value, the fold keeps at most one: the last printed
def rr.bmlist(ts: List<&2, String>, +x: String, +a: Maybe<&2, ArD.Dec>) -> {rr.B(ts, x, AutoresearchEvents.ar_mlist(a)) == AutoresearchEvents.ar_mlist(AutoresearchEvents.ar_last_value(ts, x, a)) : List<&2, ArD.Dec>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> r:
      +a2 = AutoresearchEvents.ar_value_at(ArL.metric(t), x, a)
      Equal.trans(List<&2, ArD.Dec>, rr.B(r, x, rr.bstep(ArL.metric(t), x, AutoresearchEvents.ar_mlist(a))), rr.B(r, x, AutoresearchEvents.ar_mlist(a2)), AutoresearchEvents.ar_mlist(AutoresearchEvents.ar_last_value(r, x, a2)),
        Equal.cong(List<&2, ArD.Dec>, List<&2, ArD.Dec>, c => rr.B(r, x, c), rr.bstep(ArL.metric(t), x, AutoresearchEvents.ar_mlist(a)), AutoresearchEvents.ar_mlist(a2), rr.bm1(ArL.metric(t), x, a)),
        rr.bmlist(r, x, a2))

# The looked-up value
# -------------------

def rr.pick(b: Bool, -d: ArD.Dec, -y: Maybe<&2, ArD.Dec>) -> {ArM.ar_pick(b, Some{d}, y) == AutoresearchEvents.ar_value_hit(b, d, y) : Maybe<&2, ArD.Dec>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rr.lkput(m: Maybe<&2, ArL.Kv>, +kvs: List<&2, ArL.Kv>, +x: String) -> {ArS.lookup(rr.kput(kvs, m), x) == AutoresearchEvents.ar_value_at(m, x, ArS.lookup(kvs, x)) : Maybe<&2, ArD.Dec>}:
  match m:
    case None{}:
      {==}
    case Some{kv}:
      match kv:
        case ArL.Kv{+k, +d}:
          Equal.trans(Maybe<&2, ArD.Dec>, ArS.lookup(ArS.put(kvs, k, d), x), ArM.ar_pick(String.eq(k, x), Some{d}, ArS.lookup(kvs, x)), AutoresearchEvents.ar_value_hit(String.eq(k, x), d, ArS.lookup(kvs, x)),
            ArM.metric_last_wins(kvs, k, d, x),
            rr.pick(String.eq(k, x), d, ArS.lookup(kvs, x)))

def rr.value(ts: List<&2, String>, +kvs: List<&2, ArL.Kv>, +x: String) -> {ArS.lookup(rr.lk(kvs, ts), x) == AutoresearchEvents.ar_last_value(ts, x, ArS.lookup(kvs, x)) : Maybe<&2, ArD.Dec>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> r:
      +k2 = rr.kput(kvs, ArL.metric(t))
      Equal.trans(Maybe<&2, ArD.Dec>, ArS.lookup(rr.lk(k2, r), x), AutoresearchEvents.ar_last_value(r, x, ArS.lookup(k2, x)), AutoresearchEvents.ar_last_value(r, x, AutoresearchEvents.ar_value_at(ArL.metric(t), x, ArS.lookup(kvs, x))),
        rr.value(r, k2, x),
        Equal.cong(Maybe<&2, ArD.Dec>, Maybe<&2, ArD.Dec>, c => AutoresearchEvents.ar_last_value(r, x, c), ArS.lookup(k2, x), AutoresearchEvents.ar_value_at(ArL.metric(t), x, ArS.lookup(kvs, x)), rr.lkput(ArL.metric(t), kvs, x)))

# The other metrics
# -----------------

def rr.bos.at(b: Bool, +k: String, -v: ArD.Dec, +x: String, -t: List<&2, ArL.Kv>, hb: {String.eq(k, x) == b : Bool}, ih: {AutoresearchEvents.ar_binds(ArS.others(t, x), x) == Nil{} : List<&2, ArD.Dec>}) -> {AutoresearchEvents.ar_binds(ArS.others.at(b, k, v, ArS.others(t, x)), x) == Nil{} : List<&2, ArD.Dec>}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, String.eq(k, x), False{}, hb) : {AutoresearchEvents.ar_binds.at(_, v, AutoresearchEvents.ar_binds(ArS.others(t, x), x)) == Nil{} : List<&2, ArD.Dec>}
      ih

# without name x, no value of x is left
def rr.bos(kvs: List<&2, ArL.Kv>, +x: String) -> {AutoresearchEvents.ar_binds(ArS.others(kvs, x), x) == Nil{} : List<&2, ArD.Dec>}:
  match kvs:
    case Nil{}:
      {==}
    case ArL.Kv{+k, v} <> t:
      rr.bos.at(String.eq(k, x), k, v, x, t, {==}, rr.bos(t, x))

def rr.bod.at(b: Bool, +k: String, -v: ArD.Dec, -t: List<&2, ArL.Kv>, +m: String, +x: String, hb: {String.eq(k, m) == b : Bool}, hmx: {String.eq(m, x) == False{} : Bool}, ih: {AutoresearchEvents.ar_binds(ArS.others(t, m), x) == AutoresearchEvents.ar_binds(t, x) : List<&2, ArD.Dec>}) -> {AutoresearchEvents.ar_binds(ArS.others.at(b, k, v, ArS.others(t, m)), x) == AutoresearchEvents.ar_binds.at(String.eq(k, x), v, AutoresearchEvents.ar_binds(t, x)) : List<&2, ArD.Dec>}:
  match b:
    case True{}:
      +ekx = Equal.trans(Bool, String.eq(k, x), String.eq(m, x), False{}, Equal.cong(String, Bool, y => String.eq(y, x), k, m, AS.as.str_eq(k, m, hb)), hmx)
      %Equal.sym(Bool, String.eq(k, x), False{}, ekx) : {AutoresearchEvents.ar_binds(ArS.others(t, m), x) == AutoresearchEvents.ar_binds.at(_, v, AutoresearchEvents.ar_binds(t, x)) : List<&2, ArD.Dec>}
      ih
    case False{}:
      Equal.cong(List<&2, ArD.Dec>, List<&2, ArD.Dec>, l => AutoresearchEvents.ar_binds.at(String.eq(k, x), v, l), AutoresearchEvents.ar_binds(ArS.others(t, m), x), AutoresearchEvents.ar_binds(t, x), ih)

# without another name m, the values of x stay
def rr.bod(kvs: List<&2, ArL.Kv>, +m: String, +x: String, +hmx: {String.eq(m, x) == False{} : Bool}) -> {AutoresearchEvents.ar_binds(ArS.others(kvs, m), x) == AutoresearchEvents.ar_binds(kvs, x) : List<&2, ArD.Dec>}:
  match kvs:
    case Nil{}:
      {==}
    case ArL.Kv{+k, v} <> +t:
      rr.bod.at(String.eq(k, m), k, v, t, m, x, {==}, hmx, rr.bod(t, m, x, hmx))

def rr.oth(b: Bool, +m: String, +x: String, +K: List<&2, ArL.Kv>, -ts: List<&2, String>, hb: {String.eq(m, x) == b : Bool}, kb: {AutoresearchEvents.ar_binds(K, x) == AutoresearchEvents.ar_mlist(AutoresearchEvents.ar_last_value(ts, x, None{})) : List<&2, ArD.Dec>}) -> {AutoresearchEvents.ar_binds(ArS.others(K, m), x) == AutoresearchEvents.ar_others.at(b, x, ts) : List<&2, ArD.Dec>}:
  match b:
    case True{}:
      %Equal.sym(String, m, x, AS.as.str_eq(m, x, hb)) : {AutoresearchEvents.ar_binds(ArS.others(K, _), x) == Nil{} : List<&2, ArD.Dec>}
      rr.bos(K, x)
    case False{}:
      Equal.trans(List<&2, ArD.Dec>, AutoresearchEvents.ar_binds(ArS.others(K, m), x), AutoresearchEvents.ar_binds(K, x), AutoresearchEvents.ar_mlist(AutoresearchEvents.ar_last_value(ts, x, None{})), rr.bod(K, m, x, hb), kb)

# The run's steps
# ---------------

# an accepted step answers as ev.After says
def rr.took_after(r: ArS.Res, -G: ArS.St -> Type, s: ArS.St, h: {ArM.ar_took(r) == True{} : Bool}, w: AE.ev.After(r, G)) -> G(ArM.ar_after(r, s)):
  match r:
    case ArS.Took{s2, e, stop}:
      w
    case ArS.Refuse{t}:
      AS.as.absurd(G(ArM.ar_after(ArS.Refuse{t}, s)), h)

def rr.got(m: Maybe<&2, ArL.Kv>, +cfg: Maybe<&2, ArS.Cfg>, +g: Nat, +mode: ArS.Mode, +R: List<&2, ArS.Row>, +n: Nat, +kvs: List<&2, ArL.Kv>) -> {ArM.ar_after(ArP.line.got(m, cfg, g, mode, R, n, kvs), ArS.St{cfg, g, mode, R, Some{ArS.Pend{n, kvs, None{}}}}) == ArS.St{cfg, g, mode, R, Some{ArS.Pend{n, rr.kput(kvs, m), None{}}}} : ArS.St}:
  match m:
    case None{}:
      {==}
    case Some{kv}:
      match kv:
        case ArL.Kv{k, d}:
          {==}

# the output lines reach the running run: its metrics are rr.lk's
def rr.lines(ts: List<&2, String>, -mid: List<&2, ArS.Ev>, +cfg: Maybe<&2, ArS.Cfg>, +g: Nat, +mode: ArS.Mode, +R: List<&2, ArS.Row>, +n: Nat, +kvs: List<&2, ArL.Kv>) -> {ArM.ar_run.go(List.append(&2, ArS.Ev, AutoresearchEvents.ar_lines(ts), mid), ArS.St{cfg, g, mode, R, Some{ArS.Pend{n, kvs, None{}}}}) == ArM.ar_run.go(mid, ArS.St{cfg, g, mode, R, Some{ArS.Pend{n, rr.lk(kvs, ts), None{}}}}) : ArS.St}:
  match ts:
    case Nil{}:
      {==}
    case +t <> r:
      +k2 = rr.kput(kvs, ArL.metric(t))
      %Equal.sym(ArS.St, ArM.ar_after(ArP.line.got(ArL.metric(t), cfg, g, mode, R, n, kvs), ArS.St{cfg, g, mode, R, Some{ArS.Pend{n, kvs, None{}}}}), ArS.St{cfg, g, mode, R, Some{ArS.Pend{n, k2, None{}}}}, rr.got(ArL.metric(t), cfg, g, mode, R, n, kvs)) : {ArM.ar_run.go(List.append(&2, ArS.Ev, AutoresearchEvents.ar_lines(r), mid), _) == ArM.ar_run.go(mid, ArS.St{cfg, g, mode, R, Some{ArS.Pend{n, rr.lk(k2, r), None{}}}}) : ArS.St}
      rr.lines(r, mid, cfg, g, mode, R, n, k2)

def rr.init_runs(+S: ArS.St, +c: ArS.Cfg, +f: Bool, +h: Bool, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, hi: AS.as.Init(ArS.Took{s2, eff, stop}, S, c, f, h)) -> {ArM.ar_runs(s2) == ArM.ar_runs(AS.as.InitSt(S, c, f, h)) : List<&2, ArS.Row>}:
  (p1, r1) = hi
  (p2, r2) = r1
  (p3, r3) = r2
  Equal.cong(ArS.St, List<&2, ArS.Row>, y => ArM.ar_runs(y), s2, AS.as.InitSt(S, c, f, h), p3)

def rr.log_runs(-C: Maybe<&2, ArS.Cfg>, -G: Nat, -M: ArS.Mode, -R: List<&2, ArS.Row>, -p: ArS.Pend, -st: ArS.Status, -d: String, -s2: ArS.St, hl: ArM.ar_logged(ArS.St{C, G, M, R, Some{p}}, st, d, s2)) -> {ArM.ar_runs(s2) == ArS.snoc(R, [ArM.ar_row(C, G, p, Some{st}, d)]) : List<&2, ArS.Row>}:
  (q1, rest) = hl
  q1

# the log, start or init that ends the pending run p appends its row
def rr.ends(e: ArS.Ev, +C: Maybe<&2, ArS.Cfg>, +G: Nat, +M: ArS.Mode, +R: List<&2, ArS.Row>, +p: ArS.Pend, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.step(ArS.St{C, G, M, R, Some{p}}, e) == ArS.Took{s2, eff, stop} : ArS.Res}, ends: {AutoresearchEvents.ar_ends_run(e) == True{} : Bool}) -> {ArM.ar_runs(s2) == List.append(&2, ArS.Row, R, [ArM.ar_row(C, G, p, AutoresearchEvents.ar_status_of(e), AutoresearchEvents.ar_desc_of(e))]) : List<&2, ArS.Row>}:
  match e:
    case ArS.Init{+c, +f, +h}:
      +row = ArM.ar_row(C, G, p, None{}, "")
      Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(s2), ArM.ar_runs(AS.as.InitSt(ArS.St{C, G, M, R, Some{p}}, c, f, h)), List.append(&2, ArS.Row, R, [row]),
        rr.init_runs(ArS.St{C, G, M, R, Some{p}}, c, f, h, s2, eff, stop, AS.as.init_took(ArS.St{C, G, M, R, Some{p}}, c, f, h, s2, eff, stop, ok)),
        AE.ev.app(R, [row]))
    case ArS.Begin{+m}:
      +row = ArM.ar_row(C, G, p, None{}, "")
      +x = {ArS.St{C, G, M, ArS.snoc(R, [row]), Some{ArS.Pend{m, Nil{}, None{}}}} : ArS.St}
      Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(s2), ArM.ar_runs(x), List.append(&2, ArS.Row, R, [row]),
        Equal.cong(ArS.St, List<&2, ArS.Row>, y => ArM.ar_runs(y), s2, x, AE.ev.begin_st(ArS.St{C, G, M, R, Some{p}}, m, s2, eff, stop, ok)),
        AE.ev.app(R, [row]))
    case ArS.Line{t}:
      AS.as.absurd({ArM.ar_runs(s2) == List.append(&2, ArS.Row, R, [ArM.ar_row(C, G, p, None{}, "")]) : List<&2, ArS.Row>}, ends)
    case ArS.Finish{a, b, c}:
      AS.as.absurd({ArM.ar_runs(s2) == List.append(&2, ArS.Row, R, [ArM.ar_row(C, G, p, None{}, "")]) : List<&2, ArS.Row>}, ends)
    case ArS.Log{+st, +d, +w, +v}:
      +row = ArM.ar_row(C, G, p, Some{st}, d)
      Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(s2), ArS.snoc(R, [row]), List.append(&2, ArS.Row, R, [row]), rr.log_runs(C, G, M, R, p, st, d, s2, AE.ev.logged(ArS.St{C, G, M, R, Some{p}}, st, d, w, v, s2, eff, stop, ok)), AE.ev.app(R, [row]))
    case ArS.Flag{n, r}:
      AS.as.absurd({ArM.ar_runs(s2) == List.append(&2, ArS.Row, R, [ArM.ar_row(C, G, p, None{}, "")]) : List<&2, ArS.Row>}, ends)
    case ArS.SetMode{m}:
      AS.as.absurd({ArM.ar_runs(s2) == List.append(&2, ArS.Row, R, [ArM.ar_row(C, G, p, None{}, "")]) : List<&2, ArS.Row>}, ends)

# every name x: the other metrics hold just the last value printed
def rr.oth_x(+m: String, +ts: List<&2, String>, +x: String) -> {AutoresearchEvents.ar_binds(ArS.others(rr.lk(Nil{}, ts), m), x) == AutoresearchEvents.ar_others(m, x, ts) : List<&2, ArD.Dec>}:
  +K = rr.lk(Nil{}, ts)
  rr.oth(String.eq(m, x), m, x, K, ts, {==}, Equal.trans(List<&2, ArD.Dec>, AutoresearchEvents.ar_binds(K, x), rr.B(ts, x, Nil{}), AutoresearchEvents.ar_mlist(AutoresearchEvents.ar_last_value(ts, x, None{})), rr.bfold(ts, Nil{}, x), rr.bmlist(ts, x, None{})))

def rr.tup(+n: Nat, +g: Nat, +st: Maybe<&2, ArS.Status>, +desc: String, -a: Bool, -b: Bool, -c: Bool, -d: Bool, ea: {a == c : Bool}, eb: {b == d : Bool}) -> {(n, g, st, a, b, False{}, desc) == (n, g, st, c, d, False{}, desc) : Nat & Nat & Maybe<&2, ArS.Status> & Bool & Bool & Bool & String}:
  %ea : {(n, g, st, a, b, False{}, desc) == (n, g, st, _, d, False{}, desc) : Nat & Nat & Maybe<&2, ArS.Status> & Bool & Bool & Bool & String}
  %eb : {(n, g, st, a, b, False{}, desc) == (n, g, st, a, _, False{}, desc) : Nat & Nat & Maybe<&2, ArS.Status> & Bool & Bool & Bool & String}
  {==}

# the run ended (or not) as f says before e: its row
def rr.fin(+s: ArS.St, +n: Nat, +ts: List<&2, String>, +mid: List<&2, ArS.Ev>, +e: ArS.Ev, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, +f: Maybe<&2, Bool>, ep: {ArM.ar_passed(f) == AutoresearchEvents.ar_mid_passed(mid) : Bool}, ef: {ArM.ar_ended(f) == AutoresearchEvents.ar_mid_finished(mid) : Bool}, ok: {ArP.step(rr.S(s, n, rr.lk(Nil{}, ts), f), e) == ArS.Took{s2, eff, stop} : ArS.Res}, ends: {AutoresearchEvents.ar_ends_run(e) == True{} : Bool}, er: {ArM.ar_runs(ArM.ar_after(ArP.step(s, ArS.Begin{n}), s)) == rr.R0(s) : List<&2, ArS.Row>}) -> rr.Goal(s, n, ts, mid, e, s2):
  +C = ArM.ar_cfg(s)
  +G = ArM.ar_seg(s)
  +K = rr.lk(Nil{}, ts)
  +m = ArM.ar_name(C)
  +R0 = rr.R0(s)
  +R1 = ArM.ar_runs(ArM.ar_after(ArP.step(s, ArS.Begin{n}), s))
  +row = ArM.ar_row(C, G, ArS.Pend{n, K, f}, AutoresearchEvents.ar_status_of(e), AutoresearchEvents.ar_desc_of(e))
  +eR = rr.ends(e, C, G, ArM.ar_mode(s), R0, ArS.Pend{n, K, f}, s2, eff, stop, ok, ends)
  +e1 = Equal.trans(List<&2, ArS.Row>, ArM.ar_runs(s2), List.append(&2, ArS.Row, R0, [row]), List.append(&2, ArS.Row, R1, [row]), eR,
    Equal.cong(List<&2, ArS.Row>, List<&2, ArS.Row>, l => List.append(&2, ArS.Row, l, [row]), R0, R1, Equal.sym(List<&2, ArS.Row>, R1, R0, er)))
  +tup = rr.tup(n, G, AutoresearchEvents.ar_status_of(e), AutoresearchEvents.ar_desc_of(e), ArM.ar_passed(f), ArM.ar_ended(f), AutoresearchEvents.ar_mid_passed(mid), AutoresearchEvents.ar_mid_finished(mid), ep, ef)
  (row, e1, tup, rr.value(ts, Nil{}, m), x => rr.oth_x(m, ts, x))

# what came between the output and e: nothing, or the end
def rr.mid(+s: ArS.St, +n: Nat, +ts: List<&2, String>, mid: List<&2, ArS.Ev>, +e: ArS.Ev, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, fin: {AutoresearchEvents.ar_mid_ok(mid) == True{} : Bool}, ends: {AutoresearchEvents.ar_ends_run(e) == True{} : Bool}, er: {ArM.ar_runs(ArM.ar_after(ArP.step(s, ArS.Begin{n}), s)) == rr.R0(s) : List<&2, ArS.Row>}, ok: {ArP.step(ArM.ar_run.go(mid, rr.S(s, n, rr.lk(Nil{}, ts), None{})), e) == ArS.Took{s2, eff, stop} : ArS.Res}) -> rr.Goal(s, n, ts, mid, e, s2):
  match mid:
    case Nil{}:
      rr.fin(s, n, ts, Nil{}, e, s2, eff, stop, None{}, {==}, {==}, ok, ends, er)
    case x <> rest:
      match x:
        case ArS.Init{c, f, h}:
          AS.as.absurd(rr.Goal(s, n, ts, ArS.Init{c, f, h} <> rest, e, s2), fin)
        case ArS.Begin{k}:
          AS.as.absurd(rr.Goal(s, n, ts, ArS.Begin{k} <> rest, e, s2), fin)
        case ArS.Line{t}:
          AS.as.absurd(rr.Goal(s, n, ts, ArS.Line{t} <> rest, e, s2), fin)
        case ArS.Finish{+neg, +code, +timeout}:
          match rest:
            case Nil{}:
              rr.fin(s, n, ts, [ArS.Finish{neg, code, timeout}], e, s2, eff, stop, Some{ArP.ok_exit(neg, code, timeout)}, AE.ev.exit(neg, code, timeout), {==}, ok, ends, er)
            case y <> z:
              AS.as.absurd(rr.Goal(s, n, ts, ArS.Finish{neg, code, timeout} <> (y <> z), e, s2), fin)
        case ArS.Log{st, d, w, v}:
          AS.as.absurd(rr.Goal(s, n, ts, ArS.Log{st, d, w, v} <> rest, e, s2), fin)
        case ArS.Flag{k, r}:
          AS.as.absurd(rr.Goal(s, n, ts, ArS.Flag{k, r} <> rest, e, s2), fin)
        case ArS.SetMode{m}:
          AS.as.absurd(rr.Goal(s, n, ts, ArS.SetMode{m} <> rest, e, s2), fin)

def AutoresearchEvents.run_row_is_its_output(s, n, ts, mid, e, s2, eff, stop, began, fin, ends, ok):
  +r1 = ArP.step(s, ArS.Begin{n})
  +S1 = rr.S(s, n, Nil{}, None{})
  +app = List.append(&2, ArS.Ev, AutoresearchEvents.ar_lines(ts), mid)
  +e1 = {rr.took_after(r1, x => AE.ev.BeginSt(s, n, x), s, began, AE.ev.begin.walk(s, n)) : {ArM.ar_after(r1, s) == S1 : ArS.St}}
  +er = Equal.cong(ArS.St, List<&2, ArS.Row>, y => ArM.ar_runs(y), ArM.ar_after(r1, s), S1, e1)
  +ok2 = Equal.trans(ArS.Res, ArP.step(ArM.ar_run.go(app, S1), e), ArP.step(ArM.ar_run.go(app, ArM.ar_after(r1, s)), e), ArS.Took{s2, eff, stop},
    Equal.cong(ArS.St, ArS.Res, y => ArP.step(ArM.ar_run.go(app, y), e), S1, ArM.ar_after(r1, s), Equal.sym(ArS.St, ArM.ar_after(r1, s), S1, e1)),
    ok)
  +S2 = rr.S(s, n, rr.lk(Nil{}, ts), None{})
  +el = rr.lines(ts, mid, ArM.ar_cfg(s), ArM.ar_seg(s), ArM.ar_mode(s), rr.R0(s), n, Nil{})
  +ok3 = Equal.trans(ArS.Res, ArP.step(ArM.ar_run.go(mid, S2), e), ArP.step(ArM.ar_run.go(app, S1), e), ArS.Took{s2, eff, stop},
    Equal.cong(ArS.St, ArS.Res, y => ArP.step(y, e), ArM.ar_run.go(mid, S2), ArM.ar_run.go(app, S1), Equal.sym(ArS.St, ArM.ar_run.go(app, S1), ArM.ar_run.go(mid, S2), el)),
    ok2)
  rr.mid(s, n, ts, mid, e, s2, eff, stop, fin, ends, er, ok3)
