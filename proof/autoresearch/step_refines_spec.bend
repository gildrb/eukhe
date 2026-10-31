# eukhe: the proof of LAW step_refines_spec: event by event, the code's
# step is the spec's (spec/autoresearch/step.bend); the helpers both use
# for rows and metrics are shown equal first

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/metric_line.bend as SL
import ../../spec/autoresearch/segment.bend as SG
import ../../spec/autoresearch/step.bend as SP
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/log.bend as AgLog
import ./baseline_is_first.bend as PBaselineIsFirst
import ./logged_is_segment.bend as PLoggedIsSegment

# Metrics of a run
# ----------------

def asr.lookup_at(b: Bool, -v: ArD.Dec, -r: Maybe<&2, ArD.Dec>) -> {ArS.lookup.at(b, v, r) == SP.kv_value.at(b, v, r) : Maybe<&2, ArD.Dec>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def asr.lookup(kvs: List<&2, ArL.Kv>, +x: String) -> {ArS.lookup(kvs, x) == SP.kv_value(kvs, x) : Maybe<&2, ArD.Dec>}:
  match kvs:
    case Nil{}:
      {==}
    case ArL.Kv{+k, v} <> t:
      %asr.lookup(t, x) : {ArS.lookup.at(String.eq(k, x), v, ArS.lookup(t, x)) == SP.kv_value.at(String.eq(k, x), v, _) : Maybe<&2, ArD.Dec>}
      asr.lookup_at(String.eq(k, x), v, ArS.lookup(t, x))

def asr.others_at(b: Bool, -k: String, -v: ArD.Dec, -r: List<&2, ArL.Kv>) -> {ArS.others.at(b, k, v, r) == SP.kv_drop.at(b, k, v, r) : List<&2, ArL.Kv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def asr.others(kvs: List<&2, ArL.Kv>, +x: String) -> {ArS.others(kvs, x) == SP.kv_drop(kvs, x) : List<&2, ArL.Kv>}:
  match kvs:
    case Nil{}:
      {==}
    case ArL.Kv{+k, v} <> t:
      %asr.others(t, x) : {ArS.others.at(String.eq(k, x), k, v, ArS.others(t, x)) == SP.kv_drop.at(String.eq(k, x), k, v, _) : List<&2, ArL.Kv>}
      asr.others_at(String.eq(k, x), k, v, ArS.others(t, x))

def asr.put_at(b: Bool, -k: String, -v: ArD.Dec, -t: List<&2, ArL.Kv>, -n: String, -d: ArD.Dec, -r: List<&2, ArL.Kv>) -> {ArS.put.at(b, k, v, t, n, d, r) == SP.kv_set.at(b, k, v, t, n, d, r) : List<&2, ArL.Kv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def asr.put(kvs: List<&2, ArL.Kv>, +n: String, +d: ArD.Dec) -> {ArS.put(kvs, n, d) == SP.kv_set(kvs, n, d) : List<&2, ArL.Kv>}:
  match kvs:
    case Nil{}:
      {==}
    case ArL.Kv{+k, v} <> +t:
      %asr.put(t, n, d) : {ArS.put.at(String.eq(k, n), k, v, t, n, d, ArS.put(t, n, d)) == SP.kv_set.at(String.eq(k, n), k, v, t, n, d, _) : List<&2, ArL.Kv>}
      asr.put_at(String.eq(k, n), k, v, t, n, d, ArS.put(t, n, d))

# Rows
# ----

def asr.row(+m: String, -seg: Nat, p: ArS.Pend, -st: Maybe<&2, ArS.Status>, -desc: String) -> {ArS.row(m, seg, p, st, desc) == SP.row_of(m, seg, p, st, desc) : ArS.Row}:
  match p:
    case ArS.Pend{id, +kvs, fin}:
      match fin:
        case None{}:
          %asr.lookup(kvs, m) : {ArS.Row{id, seg, st, ArS.lookup(kvs, m), ArS.others(kvs, m), False{}, False{}, False{}, desc} == ArS.Row{id, seg, st, _, SP.kv_drop(kvs, m), False{}, False{}, False{}, desc} : ArS.Row}
          %asr.others(kvs, m) : {ArS.Row{id, seg, st, ArS.lookup(kvs, m), ArS.others(kvs, m), False{}, False{}, False{}, desc} == ArS.Row{id, seg, st, ArS.lookup(kvs, m), _, False{}, False{}, False{}, desc} : ArS.Row}
          {==}
        case Some{x}:
          %asr.lookup(kvs, m) : {ArS.Row{id, seg, st, ArS.lookup(kvs, m), ArS.others(kvs, m), x, True{}, False{}, desc} == ArS.Row{id, seg, st, _, SP.kv_drop(kvs, m), x, True{}, False{}, desc} : ArS.Row}
          %asr.others(kvs, m) : {ArS.Row{id, seg, st, ArS.lookup(kvs, m), ArS.others(kvs, m), x, True{}, False{}, desc} == ArS.Row{id, seg, st, ArS.lookup(kvs, m), _, x, True{}, False{}, desc} : ArS.Row}
          {==}

def asr.gone(+m: String, -seg: Nat, pend: Maybe<&2, ArS.Pend>) -> {ArS.abandon(m, seg, pend) == SP.gone(m, seg, pend) : List<&2, ArS.Row>}:
  match pend:
    case None{}:
      {==}
    case Some{q}:
      %asr.row(m, seg, q, None{}, "") : {[ArS.row(m, seg, q, None{}, "")] == [_] : List<&2, ArS.Row>}
      {==}

def asr.app(rs: List<&2, ArS.Row>, -x: List<&2, ArS.Row>) -> {ArS.snoc(rs, x) == List.append(&2, ArS.Row, rs, x) : List<&2, ArS.Row>}:
  match rs:
    case Nil{}:
      {==}
    case h <> t:
      %asr.app(t, x) : {h <> ArS.snoc(t, x) == h <> _ : List<&2, ArS.Row>}
      {==}

# the rows after an abandon
def asr.rows_gone(+m: String, +seg: Nat, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> {ArS.snoc(runs, ArS.abandon(m, seg, pend)) == List.append(&2, ArS.Row, runs, SP.gone(m, seg, pend)) : List<&2, ArS.Row>}:
  %asr.gone(m, seg, pend) : {ArS.snoc(runs, ArS.abandon(m, seg, pend)) == List.append(&2, ArS.Row, runs, _) : List<&2, ArS.Row>}
  asr.app(runs, ArS.abandon(m, seg, pend))

# the rows after a log
def asr.rows_log(+m: String, +seg: Nat, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String) -> {ArS.snoc(runs, [ArS.row(m, seg, p, Some{st}, desc)]) == List.append(&2, ArS.Row, runs, [SP.row_of(m, seg, p, Some{st}, desc)]) : List<&2, ArS.Row>}:
  %asr.row(m, seg, p, Some{st}, desc) : {ArS.snoc(runs, [ArS.row(m, seg, p, Some{st}, desc)]) == List.append(&2, ArS.Row, runs, [_]) : List<&2, ArS.Row>}
  asr.app(runs, [ArS.row(m, seg, p, Some{st}, desc)])

def asr.len(rs: List<&2, ArS.Row>) -> {ArS.rlen(rs) == SP.count(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case h <> t:
      %asr.len(t) : {1n+ArS.rlen(t) == 1n+_ : Nat}
      {==}

def asr.next(+runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>) -> {1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)) == SP.next_id(runs, pend) : Nat}:
  match pend:
    case None{}:
      %asr.len(runs) : {1n+Nat.add(ArS.rlen(runs), 0n) == 1n+Nat.add(_, 0n) : Nat}
      {==}
    case Some{q}:
      %asr.len(runs) : {1n+Nat.add(ArS.rlen(runs), 1n) == 1n+Nat.add(_, 1n) : Nat}
      {==}

def asr.last_or(-k: Maybe<&2, ArD.Dec>, l: Maybe<&2, ArD.Dec>) -> {ArS.last.at(k, l) == SP.last_kept.or(k, l) : Maybe<&2, ArD.Dec>}:
  match l:
    case None{}:
      {==}
    case Some{x}:
      {==}

def asr.last(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArS.last(rs, seg) == SP.last_kept(rs, seg) : Maybe<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      %PBaselineIsFirst.BaselineIsFirst.kept(r, seg) : {ArS.last.at(ArS.kept(r, seg), ArS.last(t, seg)) == SP.last_kept.or(_, SP.last_kept(t, seg)) : Maybe<&2, ArD.Dec>}
      %asr.last(t, seg) : {ArS.last.at(ArS.kept(r, seg), ArS.last(t, seg)) == SP.last_kept.or(ArS.kept(r, seg), _) : Maybe<&2, ArD.Dec>}
      asr.last_or(ArS.kept(r, seg), ArS.last(t, seg))

# Init
# ----

def asr.char(c: Char, -r: Bool) -> {Bool.and(ArL.name_char(ArL.code(c)), r) == Bool.and(SL.is_name(SL.code(c)), r) : Bool}:
  match c:
    case Chr{x}:
      {==}

def asr.names(s: String) -> {ArP.name_ok.go(s) == SL.all_name(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %asr.names(t) : {Bool.and(ArL.name_char(ArL.code(c)), ArP.name_ok.go(t)) == Bool.and(SL.is_name(SL.code(c)), _) : Bool}
      asr.char(c, ArP.name_ok.go(t))

def asr.name(s: String) -> {ArP.name_ok(s) == SP.name_ok(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      asr.names(SCon{c, t})

def asr.dir(a: ArS.Dir, b: ArS.Dir) -> {ArP.dir_eq(a, b) == SP.same_dir(a, b) : Bool}:
  match a b:
    case ArS.Lower{} ArS.Lower{}:
      {==}
    case ArS.Lower{} ArS.Higher{}:
      {==}
    case ArS.Higher{} ArS.Lower{}:
      {==}
    case ArS.Higher{} ArS.Higher{}:
      {==}

def asr.set(-c: ArS.Cfg, -seg2: Nat, +m: String, +seg: Nat, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> {ArP.init.set(c, seg2, m, seg, runs, pend) == SP.opened(c, seg2, m, seg, runs, pend) : ArS.Res}:
  %asr.rows_gone(m, seg, runs, pend) : {ArP.took(ArS.St{Some{c}, seg2, ArS.On{}, ArS.snoc(runs, ArS.abandon(m, seg, pend)), None{}}) == SP.took(ArS.St{Some{c}, seg2, ArS.On{}, _, None{}}) : ArS.Res}
  {==}

def asr.need(h: Bool, -c: ArS.Cfg, -seg2: Nat, +m: String, +seg: Nat, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> {ArP.init.need(h, c, seg2, m, seg, runs, pend) == SP.init.fresh(h, c, seg2, m, seg, runs, pend) : ArS.Res}:
  match h:
    case True{}:
      asr.set(c, seg2, m, seg, runs, pend)
    case False{}:
      {==}

def asr.same(b: Bool, -c: ArS.Cfg, +m: String, +seg: Nat, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> {ArP.init.keep(b, c, m, seg, runs, pend) == SP.init.same(b, c, m, seg, runs, pend) : ArS.Res}:
  match b:
    case True{}:
      asr.set(c, seg, m, seg, runs, pend)
    case False{}:
      {==}

def asr.init_old(c: ArS.Cfg, old: Maybe<&2, ArS.Cfg>, fresh: Bool, h: Bool, +seg: Nat, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> {ArP.init.old(old, c, fresh, h, seg, runs, pend) == SP.init.after(old, c, fresh, h, seg, runs, pend) : ArS.Res}:
  match c:
    case ArS.Cfg{+a, +g, +cm, +u, +cd, +sec, +sc, +off, +mx}:
      match old:
        case None{}:
          asr.need(h, ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, seg, "", seg, runs, pend)
        case Some{o}:
          match o:
            case ArS.Cfg{oa, og, +om, ou, +od, osec, osc, ooff, omx}:
              match fresh:
                case True{}:
                  asr.need(h, ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, 1n+seg, om, seg, runs, pend)
                case False{}:
                  %asr.dir(od, cd) : {ArP.init.keep(Bool.and(String.eq(om, cm), ArP.dir_eq(od, cd)), ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, om, seg, runs, pend) == SP.init.same(Bool.and(String.eq(om, cm), _), ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, om, seg, runs, pend) : ArS.Res}
                  asr.same(Bool.and(String.eq(om, cm), ArP.dir_eq(od, cd)), ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, om, seg, runs, pend)

def asr.init_chk(b: Bool, m: Maybe<&2, Nat>, +c: ArS.Cfg, old: Maybe<&2, ArS.Cfg>, fresh: Bool, h: Bool, +seg: Nat, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> {ArP.init.check(ArP.init.err.name(b, m), old, c, fresh, h, seg, runs, pend) == SP.init.checked(b, SP.cap_ok(m), old, c, fresh, h, seg, runs, pend) : ArS.Res}:
  match b:
    case False{}:
      {==}
    case True{}:
      match m:
        case None{}:
          asr.init_old(c, old, fresh, h, seg, runs, pend)
        case Some{k}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              asr.init_old(c, old, fresh, h, seg, runs, pend)

def asr.init(c: ArS.Cfg, s: ArS.St, fresh: Bool, h: Bool) -> {ArP.init(s, c, fresh, h) == SP.init(s, c, fresh, h) : ArS.Res}:
  match c:
    case ArS.Cfg{+a, +g, +cm, +u, +cd, +sec, +sc, +off, +mx}:
      match s:
        case ArS.St{old, +seg, mode, +runs, +pend}:
          %asr.name(cm) : {ArP.init.check(ArP.init.err.name(ArP.name_ok(cm), mx), old, ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, fresh, h, seg, runs, pend) == SP.init.checked(_, SP.cap_ok(mx), old, ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, fresh, h, seg, runs, pend) : ArS.Res}
          asr.init_chk(ArP.name_ok(cm), mx, ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}, old, fresh, h, seg, runs, pend)

# A run starts, its output, its end, the mode
# -------------------------------------------

def asr.start(b: Bool, -n: Nat, c: ArS.Cfg, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> {ArP.begin.at(b, n, c, seg, mode, runs, pend) == SP.start(b, n, c, seg, mode, runs, pend) : ArS.Res}:
  match b:
    case False{}:
      {==}
    case True{}:
      match c:
        case ArS.Cfg{a, g, +cm, u, cd, sec, sc, off, mx}:
          %asr.rows_gone(cm, seg, runs, pend) : {ArP.took(ArS.St{Some{ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}}, seg, mode, ArS.snoc(runs, ArS.abandon(cm, seg, pend)), Some{ArS.Pend{n, Nil{}, None{}}}}) == SP.took(ArS.St{Some{ArS.Cfg{a, g, cm, u, cd, sec, sc, off, mx}}, seg, mode, _, Some{ArS.Pend{n, Nil{}, None{}}}}) : ArS.Res}
          {==}

def asr.begin(s: ArS.St, +run: Nat) -> {ArP.begin(s, run) == SP.begin(s, run) : ArS.Res}:
  match s:
    case ArS.St{cfg, +seg, mode, +runs, +pend}:
      match cfg:
        case None{}:
          {==}
        case Some{+c}:
          +n1 = {1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)) : Nat}
          +n2 = SP.next_id(runs, pend)
          Equal.trans(ArS.Res, ArP.begin.at(Nat.is_eq(run, n1), n1, c, seg, mode, runs, pend), SP.start(Nat.is_eq(run, n1), n1, c, seg, mode, runs, pend), SP.start(Nat.is_eq(run, n2), n2, c, seg, mode, runs, pend), asr.start(Nat.is_eq(run, n1), n1, c, seg, mode, runs, pend), Equal.cong(Nat, ArS.Res, k => SP.start(Nat.is_eq(run, k), k, c, seg, mode, runs, pend), n1, n2, asr.next(runs, pend)))

def asr.got(m: Maybe<&2, ArL.Kv>, -cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, -id: Nat, kvs: List<&2, ArL.Kv>) -> {ArP.line.got(m, cfg, seg, mode, runs, id, kvs) == SP.took(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, SP.output.kv(m, kvs), None{}}}}) : ArS.Res}:
  match m:
    case None{}:
      {==}
    case Some{kv}:
      match kv:
        case ArL.Kv{+n, +d}:
          %asr.put(kvs, n, d) : {ArP.line.got(Some{ArL.Kv{n, d}}, cfg, seg, mode, runs, id, kvs) == SP.took(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, _, None{}}}}) : ArS.Res}
          {==}

def asr.line(s: ArS.St, +text: String) -> {ArP.line(s, text) == SP.output(~ArL.metric, s, text) : ArS.Res}:
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          {==}
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case Some{x}:
                  {==}
                case None{}:
                  asr.got(ArL.metric(text), cfg, seg, mode, runs, id, kvs)

def asr.finish(s: ArS.St, -neg: Bool, -code: Nat, -timeout: Bool) -> {ArP.finish(s, neg, code, timeout) == SP.ended(s, neg, code, timeout) : ArS.Res}:
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          {==}
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case Some{x}:
                  {==}
                case None{}:
                  {==}

def asr.mode(s: ArS.St, -m: ArS.Mode) -> {ArP.set_mode(s, m) == SP.set_mode(s, m) : ArS.Res}:
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      {==}

# Flags
# -----

def asr.set_flag(r: ArS.Row) -> {ArP.flag.set(r) == SP.flagged(r) : ArS.Row}:
  match r:
    case ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      {==}

def asr.hit(r: ArS.Row, -n: Nat) -> {ArP.flag.hit(r, n) == SP.logged_as(r, n) : Bool}:
  match r:
    case ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          {==}

def asr.flag_at(b: Bool, +r: ArS.Row, +t: List<&2, ArS.Row>, +n: Nat, -rest: List<&2, ArS.Row> & Bool, ih: {rest == (SP.mark(t, n), SP.has_logged(t, n)) : List<&2, ArS.Row> & Bool}) -> {ArP.flag.at(b, r, t, rest) == (SP.mark.at(b, r, t, SP.mark(t, n)), Bool.or(b, SP.has_logged(t, n))) : List<&2, ArS.Row> & Bool}:
  match b:
    case True{}:
      %asr.set_flag(r) : {(ArP.flag.set(r) <> t, True{}) == (_ <> t, True{}) : List<&2, ArS.Row> & Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, ArS.Row> & Bool, rest, (SP.mark(t, n), SP.has_logged(t, n)), ih) : {ArP.flag.at(False{}, r, t, _) == (SP.mark.at(False{}, r, t, SP.mark(t, n)), Bool.or(False{}, SP.has_logged(t, n))) : List<&2, ArS.Row> & Bool}
      {==}

def asr.rows_flag(rs: List<&2, ArS.Row>, +n: Nat) -> {ArP.flag.rows(rs, n) == (SP.mark(rs, n), SP.has_logged(rs, n)) : List<&2, ArS.Row> & Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      Equal.trans(List<&2, ArS.Row> & Bool, ArP.flag.at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n)), (SP.mark.at(ArP.flag.hit(r, n), r, t, SP.mark(t, n)), Bool.or(ArP.flag.hit(r, n), SP.has_logged(t, n))), (SP.mark.at(SP.logged_as(r, n), r, t, SP.mark(t, n)), Bool.or(SP.logged_as(r, n), SP.has_logged(t, n))), asr.flag_at(ArP.flag.hit(r, n), r, t, n, ArP.flag.rows(t, n), asr.rows_flag(t, n)), Equal.cong(Bool, List<&2, ArS.Row> & Bool, b => (SP.mark.at(b, r, t, SP.mark(t, n)), Bool.or(b, SP.has_logged(t, n))), ArP.flag.hit(r, n), SP.logged_as(r, n), asr.hit(r, n)))

def asr.flag_end(b: Bool, -n: Nat, -cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -rs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>) -> {ArP.flag.end(b, n, cfg, seg, mode, rs, pend) == SP.flag.found(b, n, cfg, seg, mode, rs, pend) : ArS.Res}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def asr.flag_why(b: Bool, s: ArS.St, +n: Nat) -> {ArP.flag.reason(b, s, n) == SP.flag.why(b, s, n) : ArS.Res}:
  match b:
    case False{}:
      {==}
    case True{}:
      match s:
        case ArS.St{cfg, seg, mode, +runs, pend}:
          %Equal.sym(List<&2, ArS.Row> & Bool, ArP.flag.rows(runs, n), (SP.mark(runs, n), SP.has_logged(runs, n)), asr.rows_flag(runs, n)) : {ArP.flag.found(_, n, cfg, seg, mode, pend) == SP.flag.found(SP.has_logged(runs, n), n, cfg, seg, mode, SP.mark(runs, n), pend) : ArS.Res}
          asr.flag_end(SP.has_logged(runs, n), n, cfg, seg, mode, SP.mark(runs, n), pend)

def asr.flag(s: ArS.St, +n: Nat, +reason: String) -> {ArP.flag(s, n, reason) == SP.flag(s, n, reason) : ArS.Res}:
  %AgLog.ag.some_eq(reason) : {ArP.flag.reason(ArL.some(reason), s, n) == SP.flag.why(_, s, n) : ArS.Res}
  asr.flag_why(ArL.some(reason), s, n)

# Logs
# ----

def asr.cap(c: Maybe<&2, ArS.Cfg>, -n: Nat) -> {ArP.capped(c, n) == SP.at_cap(c, n) : Bool}:
  match c:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case ArS.Cfg{a, g, m, u, d, sec, sc, off, mx}:
          match mx:
            case None{}:
              {==}
            case Some{x}:
              {==}

def asr.end(stop: Bool, -cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, -eff: ArS.Eff) -> {ArP.log.end(stop, cfg, seg, mode, runs, eff) == SP.logged.with(stop, cfg, seg, mode, runs, eff) : ArS.Res}:
  match stop:
    case True{}:
      {==}
    case False{}:
      {==}

# the end of a log, on the same rows
def asr.end_rows(+cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +r: List<&2, ArS.Row>, -eff: ArS.Eff) -> {ArP.log.end(ArP.capped(cfg, ArS.logged(r, seg)), cfg, seg, mode, r, eff) == SP.logged.with(SP.at_cap(cfg, SG.logged_count(r, seg)), cfg, seg, mode, r, eff) : ArS.Res}:
  %asr.cap(cfg, SG.logged_count(r, seg)) : {ArP.log.end(ArP.capped(cfg, ArS.logged(r, seg)), cfg, seg, mode, r, eff) == SP.logged.with(_, cfg, seg, mode, r, eff) : ArS.Res}
  %PLoggedIsSegment.LoggedIsSegment.go(r, seg) : {ArP.log.end(ArP.capped(cfg, ArS.logged(r, seg)), cfg, seg, mode, r, eff) == SP.logged.with(ArP.capped(cfg, _), cfg, seg, mode, r, eff) : ArS.Res}
  asr.end(ArP.capped(cfg, ArS.logged(r, seg)), cfg, seg, mode, r, eff)

def asr.done_m(+m: String, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String, -eff: ArS.Eff) -> {ArP.log.end(ArP.capped(cfg, ArS.logged(ArS.snoc(runs, [ArS.row(m, seg, p, Some{st}, desc)]), seg)), cfg, seg, mode, ArS.snoc(runs, [ArS.row(m, seg, p, Some{st}, desc)]), eff) == SP.logged.with(SP.at_cap(cfg, SG.logged_count(List.append(&2, ArS.Row, runs, [SP.row_of(m, seg, p, Some{st}, desc)]), seg)), cfg, seg, mode, List.append(&2, ArS.Row, runs, [SP.row_of(m, seg, p, Some{st}, desc)]), eff) : ArS.Res}:
  +r1 = ArS.snoc(runs, [ArS.row(m, seg, p, Some{st}, desc)])
  +r2 = List.append(&2, ArS.Row, runs, [SP.row_of(m, seg, p, Some{st}, desc)])
  Equal.trans(ArS.Res, ArP.log.end(ArP.capped(cfg, ArS.logged(r1, seg)), cfg, seg, mode, r1, eff), SP.logged.with(SP.at_cap(cfg, SG.logged_count(r1, seg)), cfg, seg, mode, r1, eff), SP.logged.with(SP.at_cap(cfg, SG.logged_count(r2, seg)), cfg, seg, mode, r2, eff), asr.end_rows(cfg, seg, mode, r1, eff), Equal.cong(List<&2, ArS.Row>, ArS.Res, r => SP.logged.with(SP.at_cap(cfg, SG.logged_count(r, seg)), cfg, seg, mode, r, eff), r1, r2, asr.rows_log(m, seg, runs, p, st, desc)))

def asr.done(cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String, -eff: ArS.Eff) -> {ArP.log.done(cfg, seg, mode, runs, p, st, desc, eff) == SP.logged(cfg, seg, mode, runs, p, st, desc, eff) : ArS.Res}:
  match cfg:
    case None{}:
      asr.done_m("", None{}, seg, mode, runs, p, st, desc, eff)
    case Some{k}:
      match k:
        case ArS.Cfg{a, g, +cm, u, d, sec, sc, off, mx}:
          asr.done_m(cm, Some{ArS.Cfg{a, g, cm, u, d, sec, sc, off, mx}}, seg, mode, runs, p, st, desc, eff)

def asr.why(w: Maybe<&2, String>) -> {ArP.justified(w) == SP.why_given(w) : Bool}:
  match w:
    case None{}:
      {==}
    case Some{t}:
      AgLog.ag.some_eq(t)

def asr.worse(-x: ArD.Dec, b: Maybe<&2, ArD.Dec>, d: ArS.Dir) -> {ArP.t_worse(x, b, d) == SP.not_better(~ArD.show, x, b, d) : String}:
  match b d:
    case None{} ArS.Lower{}:
      {==}
    case None{} ArS.Higher{}:
      {==}
    case Some{y} ArS.Lower{}:
      {==}
    case Some{y} ArS.Higher{}:
      {==}

def asr.kscope(b: Bool, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String) -> {ArP.keep.why(b, cfg, seg, mode, runs, p, desc) == SP.keep.scope(b, cfg, seg, mode, runs, p, desc) : ArS.Res}:
  match b:
    case False{}:
      {==}
    case True{}:
      asr.done(cfg, seg, mode, runs, p, ArS.Keep{}, desc, ArS.Commit{})

def asr.kbetter(b: Bool, +x: ArD.Dec, +dir: ArS.Dir, +why: Maybe<&2, String>, +devs: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String) -> {ArP.keep.beats(b, x, dir, why, devs, cfg, seg, mode, runs, p, desc) == SP.keep.better(~ArD.show, b, x, dir, why, devs, cfg, seg, mode, runs, p, desc) : ArS.Res}:
  match b:
    case False{}:
      %asr.last(runs, seg) : {ArS.Refuse{ArP.t_worse(x, ArS.last(runs, seg), dir)} == ArS.Refuse{SP.not_better(~ArD.show, x, _, dir)} : ArS.Res}
      Equal.cong(String, ArS.Res, t => ArS.Refuse{t}, ArP.t_worse(x, ArS.last(runs, seg), dir), SP.not_better(~ArD.show, x, ArS.last(runs, seg), dir), asr.worse(x, ArS.last(runs, seg), dir))
    case True{}:
      %asr.why(why) : {ArP.keep.why(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), cfg, seg, mode, runs, p, desc) == SP.keep.scope(Bool.or(Nat.is_eq(devs, 0n), _), cfg, seg, mode, runs, p, desc) : ArS.Res}
      asr.kscope(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), cfg, seg, mode, runs, p, desc)

def asr.kmetric(c: ArS.Cfg, m: Maybe<&2, ArD.Dec>, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String) -> {ArP.keep.metric(m, c, why, devs, seg, mode, runs, p, desc) == SP.keep.metric(~ArD.Dec.cmp, ~ArD.show, m, c, why, devs, seg, mode, runs, p, desc) : ArS.Res}:
  match c:
    case ArS.Cfg{+a, +g, +cm, +u, +dir, +sec, +sc, +off, +mx}:
      match m:
        case None{}:
          {==}
        case Some{+x}:
          %AgLog.ag.beats_eq(dir, x, runs, seg) : {ArP.keep.beats(ArS.beats(dir, x, runs, seg), x, dir, why, devs, Some{ArS.Cfg{a, g, cm, u, dir, sec, sc, off, mx}}, seg, mode, runs, p, desc) == SP.keep.better(~ArD.show, _, x, dir, why, devs, Some{ArS.Cfg{a, g, cm, u, dir, sec, sc, off, mx}}, seg, mode, runs, p, desc) : ArS.Res}
          asr.kbetter(ArS.beats(dir, x, runs, seg), x, dir, why, devs, Some{ArS.Cfg{a, g, cm, u, dir, sec, sc, off, mx}}, seg, mode, runs, p, desc)

def asr.keep(passed: Bool, cfg: Maybe<&2, ArS.Cfg>, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +desc: String) -> {ArP.keep(passed, cfg, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, desc) == SP.keep(~ArD.Dec.cmp, ~ArD.show, passed, cfg, why, devs, seg, mode, runs, id, kvs, desc) : ArS.Res}:
  match passed:
    case False{}:
      {==}
    case True{}:
      match cfg:
        case None{}:
          {==}
        case Some{c}:
          match c:
            case ArS.Cfg{+a, +g, +cm, +u, +dir, +sec, +sc, +off, +mx}:
              %asr.lookup(kvs, cm) : {ArP.keep.metric(ArS.lookup(kvs, cm), ArS.Cfg{a, g, cm, u, dir, sec, sc, off, mx}, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) == SP.keep.metric(~ArD.Dec.cmp, ~ArD.show, _, ArS.Cfg{a, g, cm, u, dir, sec, sc, off, mx}, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) : ArS.Res}
              asr.kmetric(ArS.Cfg{a, g, cm, u, dir, sec, sc, off, mx}, ArS.lookup(kvs, cm), why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc)

def asr.crash(passed: Bool, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +desc: String, -why: Maybe<&2, String>, -devs: Nat) -> {ArP.log.status(ArS.Crash{}, passed, desc, why, devs, cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}) == SP.log.of(~ArD.Dec.cmp, ~ArD.show, ArS.Crash{}, passed, desc, why, devs, cfg, seg, mode, runs, id, kvs) : ArS.Res}:
  match passed:
    case True{}:
      {==}
    case False{}:
      asr.done(cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{False{}}}, ArS.Crash{}, desc, ArS.Reset{})

def asr.checks(passed: Bool, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +desc: String, -why: Maybe<&2, String>, -devs: Nat) -> {ArP.log.status(ArS.Checks{}, passed, desc, why, devs, cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}) == SP.log.of(~ArD.Dec.cmp, ~ArD.show, ArS.Checks{}, passed, desc, why, devs, cfg, seg, mode, runs, id, kvs) : ArS.Res}:
  match passed:
    case False{}:
      {==}
    case True{}:
      asr.done(cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, ArS.Checks{}, desc, ArS.Reset{})

def asr.log(s: ArS.St, st: ArS.Status, +desc: String, +why: Maybe<&2, String>, +devs: Nat) -> {ArP.log(s, st, desc, why, devs) == SP.log(~ArD.Dec.cmp, ~ArD.show, s, st, desc, why, devs) : ArS.Res}:
  match s:
    case ArS.St{+cfg, +seg, mode, +runs, pend}:
      match pend:
        case None{}:
          {==}
        case Some{p}:
          match p:
            case ArS.Pend{+id, +kvs, fin}:
              match fin:
                case None{}:
                  {==}
                case Some{+passed}:
                  match st:
                    case ArS.Keep{}:
                      asr.keep(passed, cfg, why, devs, seg, mode, runs, id, kvs, desc)
                    case ArS.Discard{}:
                      asr.done(cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Discard{}, desc, ArS.Reset{})
                    case ArS.Crash{}:
                      asr.crash(passed, cfg, seg, mode, runs, id, kvs, desc, why, devs)
                    case ArS.Checks{}:
                      asr.checks(passed, cfg, seg, mode, runs, id, kvs, desc, why, devs)

# The step
# --------

def Autoresearch.step_refines_spec(s, e):
  match e:
    case ArS.Init{c, fresh, harness}:
      asr.init(c, s, fresh, harness)
    case ArS.Begin{n}:
      asr.begin(s, n)
    case ArS.Line{text}:
      asr.line(s, text)
    case ArS.Finish{neg, code, timeout}:
      asr.finish(s, neg, code, timeout)
    case ArS.Log{st, desc, why, devs}:
      asr.log(s, st, desc, why, devs)
    case ArS.Flag{n, reason}:
      asr.flag(s, n, reason)
    case ArS.SetMode{m}:
      asr.mode(s, m)
