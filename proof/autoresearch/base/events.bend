# eukhe: lemmas the proofs of laws/autoresearch/events.bend (and the
# history laws built on them) share: the code's tests against the laws'
# words, and the state each accepted event leaves

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../../../spec/autoresearch/metric_line.bend as SL
import ../../../laws/autoresearch/model.bend as ArM
import ../../../laws/autoresearch/events.bend as AutoresearchEvents
import ./step.bend as AS
import ./log.bend as AgLog
import ./accept.bend as AA

# Logic
# -----

def ev.unwrap(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def ev.some_inj(-A: Data, +a: A, b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => ev.unwrap(A, a, m), Some{a}, Some{b}, e)

def ev.MN(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# no value is nothing: anything follows
def ev.none_some(-A: Data, -G: Type, -b: A, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  %e : ev.MN(A, _, G)
  Unit{}

def ev.some_none(-A: Data, -G: Type, -b: A, e: {Some{b} == None{} : Maybe<&2, A>}) -> G:
  ev.none_some(A, G, b, Equal.sym(Maybe<&2, A>, Some{b}, None{}, e))

def ev.bnot(b: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      True{}

# Some{True} is not Some{False}
def ev.tf(-G: Type, e: {Some{True{}} == Some{False{}} : Maybe<&2, Bool>}) -> G:
  AS.as.absurd_tf(G, ev.some_inj(Bool, True{}, False{}, e))

def ev.ft(-G: Type, e: {Some{False{}} == Some{True{}} : Maybe<&2, Bool>}) -> G:
  AS.as.absurd(G, ev.some_inj(Bool, False{}, True{}, e))

def ev.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Rows
# ----

# the code's snoc is the append the laws speak of
def ev.app(rs: List<&2, ArS.Row>, -ys: List<&2, ArS.Row>) -> {ArS.snoc(rs, ys) == List.append(&2, ArS.Row, rs, ys) : List<&2, ArS.Row>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      Equal.cong(List<&2, ArS.Row>, List<&2, ArS.Row>, x => r <> x, ArS.snoc(t, ys), List.append(&2, ArS.Row, t, ys), ev.app(t, ys))

def ev.app_nil(rs: List<&2, ArS.Row>) -> {rs == List.append(&2, ArS.Row, rs, Nil{}) : List<&2, ArS.Row>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      Equal.cong(List<&2, ArS.Row>, List<&2, ArS.Row>, x => r <> x, t, List.append(&2, ArS.Row, t, Nil{}), ev.app_nil(t))

# the rows a pending run leaves when abandoned, under any metric name
def ev.abandons(-c: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, +m: String) -> AutoresearchEvents.ar_abandons(ArS.St{c, seg, mode, runs, pend}, ArS.snoc(runs, ArS.abandon(m, seg, pend))):
  match pend:
    case None{}:
      Equal.trans(List<&2, ArS.Row>, ArS.snoc(runs, Nil{}), List.append(&2, ArS.Row, runs, Nil{}), runs, ev.app(runs, Nil{}), Equal.sym(List<&2, ArS.Row>, runs, List.append(&2, ArS.Row, runs, Nil{}), ev.app_nil(runs)))
    case Some{p}:
      match p:
        case ArS.Pend{+id, +kvs, fin}:
          match fin:
            case None{}:
              (ArS.row(m, seg, ArS.Pend{id, kvs, None{}}, None{}, ""), (ev.app(runs, [ArS.row(m, seg, ArS.Pend{id, kvs, None{}}, None{}, "")]), {==}))
            case Some{+b}:
              (ArS.row(m, seg, ArS.Pend{id, kvs, Some{b}}, None{}, ""), (ev.app(runs, [ArS.row(m, seg, ArS.Pend{id, kvs, Some{b}}, None{}, "")]), {==}))

# Init
# ----

def ev.name(+m: String, b: Bool, h: {AutoresearchEvents.ar_name_ok(m) == b : Bool}) -> {ArP.name_ok(m) == b : Bool}:
  Equal.trans(Bool, ArP.name_ok(m), Bool.and(SL.nonempty(m), SL.all_name(m)), b, Equal.sym(Bool, Bool.and(SL.nonempty(m), SL.all_name(m)), ArP.name_ok(m), AS.as.name(m)), h)

def ev.cap(+m: Maybe<&2, Nat>, b: Bool, h: {ArM.ar_cap_ok(m) == b : Bool}) -> {ArP.cap_ok(m) == b : Bool}:
  Equal.trans(Bool, ArP.cap_ok(m), ArM.ar_cap_ok(m), b, Equal.sym(Bool, ArM.ar_cap_ok(m), ArP.cap_ok(m), AS.as.cap(m)), h)

# a configuration with a METRIC name and a cap of at least 1 has no error
def ev.err_none(+c: ArS.Cfg, name: {AutoresearchEvents.ar_name_ok(ArS.Cfg.metric(c)) == True{} : Bool}, cap: {ArM.ar_cap_ok(ArS.Cfg.max(c)) == True{} : Bool}) -> {ArP.init.err(c) == None{} : Maybe<&2, String>}:
  %Equal.sym(Bool, ArP.name_ok(ArS.Cfg.metric(c)), True{}, ev.name(ArS.Cfg.metric(c), True{}, name)) : {ArP.init.err.name(_, ArS.Cfg.max(c)) == None{} : Maybe<&2, String>}
  %Equal.sym(Bool, ArP.cap_ok(ArS.Cfg.max(c)), True{}, ev.cap(ArS.Cfg.max(c), True{}, cap)) : {ArP.init.err.max(_) == None{} : Maybe<&2, String>}
  {==}

def ev.dir(a: ArS.Dir, b: ArS.Dir) -> {ArP.dir_eq(a, b) == ArM.ar_dir_eq(a, b) : Bool}:
  match a b:
    case ArS.Lower{} ArS.Lower{}:
      {==}
    case ArS.Lower{} ArS.Higher{}:
      {==}
    case ArS.Higher{} ArS.Lower{}:
      {==}
    case ArS.Higher{} ArS.Higher{}:
      {==}

# the code's same kind is the law's
def ev.same(+o: ArS.Cfg, +c: ArS.Cfg) -> {ArP.same(o, c) == Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), ArM.ar_dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c))) : Bool}:
  Equal.cong(Bool, Bool, x => Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), x), ArP.dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c)), ArM.ar_dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c)), ev.dir(ArS.Cfg.dir(o), ArS.Cfg.dir(c)))

# What accepted steps leave
# -------------------------

# a G about the state after an accepted step, trivial at a refusal
def ev.After(r: ArS.Res, G: ArS.St -> Type) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      G(s2)
    case ArS.Refuse{t}:
      Unit

def ev.after(-r: ArS.Res, -G: ArS.St -> Type, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {r == ArS.Took{s2, eff, stop} : ArS.Res}, h: ev.After(r, G)) -> G(s2):
  %ok : ev.After(_, G)
  h

# the state an accepted start leaves
def ev.BeginSt(+s: ArS.St, +n: Nat, s2: ArS.St) -> Type:
  {s2 == ArS.St{ArM.ar_cfg(s), ArM.ar_seg(s), ArM.ar_mode(s), ArS.snoc(ArM.ar_runs(s), ArM.ar_gone(s)), Some{ArS.Pend{n, Nil{}, None{}}}} : ArS.St}

def ev.begin.at(b: Bool, +r: Nat, +n: Nat, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, eb: {Nat.is_eq(r, n) == b : Bool}) -> ev.After(ArP.begin.at(b, n, c, seg, mode, runs, pend), s2 => ev.BeginSt(ArS.St{Some{c}, seg, mode, runs, pend}, r, s2)):
  match b:
    case True{}:
      %AS.as.gone(Some{c}, seg, mode, runs, pend) : {ArS.St{Some{c}, seg, mode, ArS.snoc(runs, ArS.abandon(ArS.Cfg.metric(c), seg, pend)), Some{ArS.Pend{n, Nil{}, None{}}}} == ArS.St{Some{c}, seg, mode, ArS.snoc(runs, _), Some{ArS.Pend{r, Nil{}, None{}}}} : ArS.St}
      %AS.as.nat_eq(r, n, eb) : {ArS.St{Some{c}, seg, mode, ArS.snoc(runs, ArS.abandon(ArS.Cfg.metric(c), seg, pend)), Some{ArS.Pend{_, Nil{}, None{}}}} == ArS.St{Some{c}, seg, mode, ArS.snoc(runs, ArS.abandon(ArS.Cfg.metric(c), seg, pend)), Some{ArS.Pend{r, Nil{}, None{}}}} : ArS.St}
      {==}
    case False{}:
      Unit{}

def ev.begin.walk(s: ArS.St, +n: Nat) -> ev.After(ArP.step(s, ArS.Begin{n}), s2 => ev.BeginSt(s, n, s2)):
  match s:
    case ArS.St{cfg, +seg, +mode, +runs, +pend}:
      match cfg:
        case None{}:
          Unit{}
        case Some{+c}:
          ev.begin.at(Nat.is_eq(n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))), n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), c, seg, mode, runs, pend, {==})

def ev.begin_st(+s: ArS.St, +n: Nat, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.step(s, ArS.Begin{n}) == ArS.Took{s2, eff, stop} : ArS.Res}) -> ev.BeginSt(s, n, s2):
  ev.after(ArP.step(s, ArS.Begin{n}), s2 => ev.BeginSt(s, n, s2), s2, eff, stop, ok, ev.begin.walk(s, n))

# a line, an end or the mode keeps the configuration, segment and rows
def ev.Same(+s: ArS.St, s2: ArS.St) -> Type:
  {ArM.ar_cfg(s2) == ArM.ar_cfg(s) : Maybe<&2, ArS.Cfg>} & ({ArM.ar_seg(s2) == ArM.ar_seg(s) : Nat} & {ArM.ar_runs(s2) == ArM.ar_runs(s) : List<&2, ArS.Row>})

def ev.line.got(m: Maybe<&2, ArL.Kv>, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, id: Nat, kvs: List<&2, ArL.Kv>) -> ev.After(ArP.line.got(m, cfg, seg, mode, runs, id, kvs), s2 => ev.Same(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, s2)):
  match m:
    case None{}:
      ({==}, ({==}, {==}))
    case Some{kv}:
      match kv:
        case ArL.Kv{n, d}:
          ({==}, ({==}, {==}))

def ev.line.walk(s: ArS.St, +t: String) -> ev.After(ArP.step(s, ArS.Line{t}), s2 => ev.Same(s, s2)):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, pend}:
      match pend:
        case None{}:
          Unit{}
        case Some{p}:
          match p:
            case ArS.Pend{+id, +kvs, fin}:
              match fin:
                case Some{b}:
                  Unit{}
                case None{}:
                  ev.line.got(ArL.metric(t), cfg, seg, mode, runs, id, kvs)

def ev.finish.walk(s: ArS.St, -neg: Bool, -code: Nat, -timeout: Bool) -> ev.After(ArP.step(s, ArS.Finish{neg, code, timeout}), s2 => ev.Same(s, s2)):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, pend}:
      match pend:
        case None{}:
          Unit{}
        case Some{p}:
          match p:
            case ArS.Pend{+id, +kvs, fin}:
              match fin:
                case Some{b}:
                  Unit{}
                case None{}:
                  ({==}, ({==}, {==}))

def ev.mode.walk(s: ArS.St, -m: ArS.Mode) -> ev.After(ArP.step(s, ArS.SetMode{m}), s2 => ev.Same(s, s2)):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, +pend}:
      ({==}, ({==}, {==}))

def ev.fst(p: List<&2, ArS.Row> & Bool) -> List<&2, ArS.Row>:
  (a, b) = p
  a

def ev.snd(p: List<&2, ArS.Row> & Bool) -> Bool:
  (a, b) = p
  b

# the state an accepted flag leaves
def ev.FlagSt(+s: ArS.St, +n: Nat, s2: ArS.St) -> Type:
  {s2 == ArS.St{ArM.ar_cfg(s), ArM.ar_seg(s), ArM.ar_mode(s), ev.fst(ArP.flag.rows(ArM.ar_runs(s), n)), ArM.ar_pend(s)} : ArS.St}

def ev.flag.end(f: Bool, -n: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +a: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> ev.After(ArP.flag.end(f, n, cfg, seg, mode, a, pend), s2 => {s2 == ArS.St{cfg, seg, mode, a, pend} : ArS.St}):
  match f:
    case True{}:
      {==}
    case False{}:
      Unit{}

def ev.flag.found(q: List<&2, ArS.Row> & Bool, -n: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +pend: Maybe<&2, ArS.Pend>) -> ev.After(ArP.flag.found(q, n, cfg, seg, mode, pend), s2 => {s2 == ArS.St{cfg, seg, mode, ev.fst(q), pend} : ArS.St}):
  match q:
    case (a, f):
      ev.flag.end(f, n, cfg, seg, mode, a, pend)

def ev.flag.reason(ok: Bool, s: ArS.St, +n: Nat) -> ev.After(ArP.flag.reason(ok, s, n), s2 => ev.FlagSt(s, n, s2)):
  match ok:
    case True{}:
      match s:
        case ArS.St{+cfg, +seg, +mode, +runs, +pend}:
          ev.flag.found(ArP.flag.rows(runs, n), n, cfg, seg, mode, pend)
    case False{}:
      Unit{}

def ev.flag.walk(+s: ArS.St, +n: Nat, reason: String) -> ev.After(ArP.step(s, ArS.Flag{n, reason}), s2 => ev.FlagSt(s, n, s2)):
  ev.flag.reason(ArL.some(reason), s, n)

# an accepted log appends the pending run's row (ArM.ar_logged)
def ev.logged(s: ArS.St, st: ArS.Status, +desc: String, +why: Maybe<&2, String>, +devs: Nat, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.step(s, ArS.Log{st, desc, why, devs}) == ArS.Took{s2, eff, stop} : ArS.Res}) -> ArM.ar_logged(s, st, desc, s2):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, pend}:
      match pend:
        case None{}:
          AgLog.ag.refused(Empty, ArP.t_no_run(), s2, eff, stop, ok)
        case Some{p}:
          match p:
            case ArS.Pend{+id, +kvs, fin}:
              match fin:
                case None{}:
                  AgLog.ag.refused(ArM.ar_logged(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, st, desc, s2), ArP.t_running(), s2, eff, stop, ok)
                case Some{+passed}:
                  match st:
                    case ArS.Keep{}:
                      AgLog.ag.keep_done(passed, cfg, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, desc, s2, eff, stop, ok)
                    case ArS.Discard{}:
                      AgLog.ag.done(cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Discard{}, desc, ArS.Reset{}, s2, eff, stop, ok)
                    case ArS.Crash{}:
                      AgLog.ag.need_done(Bool.not(passed), ArP.t_passed(), cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Crash{}, desc, s2, eff, stop, ok)
                    case ArS.Checks{}:
                      AgLog.ag.need_done(passed, ArP.t_failed(), cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Checks{}, desc, s2, eff, stop, ok)

# the code's text of a best and of a direction are the law's
def ev.best_text(b: Maybe<&2, ArD.Dec>) -> {ArP.t_best(b) == AutoresearchEvents.ar_best_text(b) : String}:
  match b:
    case None{}:
      {==}
    case Some{x}:
      {==}

def ev.dir_word(d: ArS.Dir) -> {ArP.t_dir(d) == AutoresearchEvents.ar_dir_word(d) : String}:
  match d:
    case ArS.Lower{}:
      {==}
    case ArS.Higher{}:
      {==}

def ev.just(w: Maybe<&2, String>) -> {ArP.justified(w) == ArM.ar_justified(w) : Bool}:
  match w:
    case None{}:
      {==}
    case Some{t}:
      AgLog.ag.some_eq(t)

# the code's exit test is the law's
def ev.exit(neg: Bool, code: Nat, timeout: Bool) -> {ArP.ok_exit(neg, code, timeout) == AutoresearchEvents.ar_exit_passed(neg, code, timeout) : Bool}:
  match neg:
    case True{}:
      match code:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case False{}:
      match code:
        case 0n:
          {==}
        case 1n+k:
          {==}
