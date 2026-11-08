# eukhe: the laws of area autoresearch: the model (bend/autoresearch/;
# port of oh-my-pi autoresearch). Each law is a claim about the shipped
# rule: the METRIC line parser and the decimal order (autoresearch/line,
# autoresearch/dec), one step on the state (autoresearch/step), the
# state's metrics (autoresearch/state, autoresearch/stats), or a history
# of steps from the empty state (the host replays its event log so). The
# entry's laws (laws/autoresearch/entry.bend) tie the stepper to them.

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../spec/autoresearch/decimal.bend as SD
import ../../spec/autoresearch/metric_line.bend as SL
import ../../spec/autoresearch/segment.bend as SG
import ../../spec/autoresearch/stats.bend as SS
import ../../spec/autoresearch/step.bend as SP

# Terms
# -----

# the state after a step's answer: the new one, or the old one on a
# refusal
def ar_after(r: ArS.Res, s: ArS.St) -> ArS.St:
  match r:
    case ArS.Took{s2, e, stop}:
      s2
    case ArS.Refuse{t}:
      s

def ar_run.go(evs: List<&2, ArS.Ev>, +s: ArS.St) -> ArS.St:
  match evs:
    case Nil{}:
      s
    case e <> t:
      ar_run.go(t, ar_after(ArP.step(s, e), s))

# the state the events evs leave, from the empty state (the host's replay)
def ar_run(evs: List<&2, ArS.Ev>) -> ArS.St:
  ar_run.go(evs, ArS.St.empty())

def ar_cfg(s: ArS.St) -> Maybe<&2, ArS.Cfg>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      c

def ar_seg(s: ArS.St) -> Nat:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      seg

def ar_mode(s: ArS.St) -> ArS.Mode:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      mode

def ar_runs(s: ArS.St) -> List<&2, ArS.Row>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      runs

def ar_pend(s: ArS.St) -> Maybe<&2, ArS.Pend>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      pend

# how the pending run ended: none (no run, or it runs), or passed or not
def ar_fin(s: ArS.St) -> Maybe<&2, Bool>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          None{}
        case Some{ArS.Pend{id, kvs, fin}}:
          fin

def ar_name(c: Maybe<&2, ArS.Cfg>) -> String:
  match c:
    case None{}:
      ""
    case Some{k}:
      ArS.Cfg.metric(k)

def ar_passed(f: Maybe<&2, Bool>) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{p}:
      p

def ar_ended(f: Maybe<&2, Bool>) -> Bool:
  match f:
    case None{}:
      False{}
    case Some{p}:
      True{}

# the row of pending run p, in segment seg under configuration c, with a
# status and a description: its metric is the one its output printed
def ar_row(+c: Maybe<&2, ArS.Cfg>, seg: Nat, p: ArS.Pend, st: Maybe<&2, ArS.Status>, desc: String) -> ArS.Row:
  match p:
    case ArS.Pend{id, +kvs, +fin}:
      ArS.Row{id, seg, st, ArS.lookup(kvs, ar_name(c)), ArS.others(kvs, ar_name(c)), ar_passed(fin), ar_ended(fin), False{}, desc}

# the rows a pending run leaves when a start or an init abandons it
def ar_gone(s: ArS.St) -> List<&2, ArS.Row>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          Nil{}
        case Some{p}:
          [ar_row(c, seg, p, None{}, "")]

def ar_count_runs(rs: List<&2, ArS.Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      1n+ar_count_runs(t)

# how many runs started: the ended ones and the pending one
def ar_started(s: ArS.St) -> Nat:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          ar_count_runs(runs)
        case Some{p}:
          1n+ar_count_runs(runs)

# the event is a log, a flag, a start
def ar_is_log(e: ArS.Ev) -> Bool:
  match e:
    case ArS.Init{c, f, h}:
      False{}
    case ArS.Begin{n}:
      False{}
    case ArS.Line{t}:
      False{}
    case ArS.Finish{n, c, t}:
      False{}
    case ArS.Log{st, d, w, v}:
      True{}
    case ArS.Flag{n, r}:
      False{}
    case ArS.SetMode{m}:
      False{}

def ar_is_flag(e: ArS.Ev) -> Bool:
  match e:
    case ArS.Init{c, f, h}:
      False{}
    case ArS.Begin{n}:
      False{}
    case ArS.Line{t}:
      False{}
    case ArS.Finish{n, c, t}:
      False{}
    case ArS.Log{st, d, w, v}:
      False{}
    case ArS.Flag{n, r}:
      True{}
    case ArS.SetMode{m}:
      False{}

def ar_is_begin(e: ArS.Ev) -> Bool:
  match e:
    case ArS.Init{c, f, h}:
      False{}
    case ArS.Begin{n}:
      True{}
    case ArS.Line{t}:
      False{}
    case ArS.Finish{n, c, t}:
      False{}
    case ArS.Log{st, d, w, v}:
      False{}
    case ArS.Flag{n, r}:
      False{}
    case ArS.SetMode{m}:
      False{}

def ar_took(r: ArS.Res) -> Bool:
  match r:
    case ArS.Took{s2, e, stop}:
      True{}
    case ArS.Refuse{t}:
      False{}

def ar_one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# Metrics
# -------

# LAW metric_order_exact: the shipped order of two well-formed decimals
# is the order of their values: ±num(ds)/10^scale, compared by
# arithmetic (spec/autoresearch/decimal.bend), whatever their scales,
# signs or leading and trailing zeros
# EXCLUDES: digits compared as text (9 > 10), scales ignored (1.5 > 2), a
# sign ignored or reversed, -0 below 0, a shorter number read as smaller
# after the point (0.5 < 0.25)
law metric_order_exact:
  for +a: ArD.Dec
  for +b: ArD.Dec
  for wa: {SD.Wf(a) == True{} : Bool}
  for wb: {SD.Wf(b) == True{} : Bool}
  {ArD.Dec.cmp(a, b) == SD.order(a, b) : Cmp}

def ar_flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# LAW metric_order_reverse: the shipped order of b and a is the order of
# a and b turned around, for any decimals
# EXCLUDES: an order whose two directions disagree (a keep that beats the
# best while the best also beats it)
law metric_order_reverse:
  for +a: ArD.Dec
  for +b: ArD.Dec
  {ArD.Dec.cmp(b, a) == ar_flip(ArD.Dec.cmp(a, b)) : Cmp}

# LAW metric_order_self: every decimal is equal to itself in the shipped
# order
# EXCLUDES: a metric better than itself (a keep that beats its own
# baseline)
law metric_order_self:
  for +a: ArD.Dec
  {ArD.Dec.cmp(a, a) == EQ{} : Cmp}

# LAW metric_order_example: anchor: 12.5 < 13, 99.5 < 100, -0.5 < 0,
# -2 < -1.5, 0.10 = 0.1, -0 = 0
# EXCLUDES: an order that misses one of the cases above
law metric_order_example:
  {[ArD.Dec.cmp(ArD.Dec{False{}, [1n, 2n, 5n], 1n}, ArD.Dec{False{}, [1n, 3n], 0n}), ArD.Dec.cmp(ArD.Dec{False{}, [9n, 9n, 5n], 1n}, ArD.Dec{False{}, [1n, 0n, 0n], 0n}), ArD.Dec.cmp(ArD.Dec{True{}, [5n], 1n}, ArD.Dec{False{}, [], 0n}), ArD.Dec.cmp(ArD.Dec{True{}, [2n], 0n}, ArD.Dec{True{}, [1n, 5n], 1n}), ArD.Dec.cmp(ArD.Dec{False{}, [1n, 0n], 2n}, ArD.Dec{False{}, [1n], 1n}), ArD.Dec.cmp(ArD.Dec{True{}, [0n], 0n}, ArD.Dec{False{}, [], 0n})] == [LT{}, LT{}, LT{}, LT{}, EQ{}, EQ{}] : List<&2, Cmp>}

# LAW metric_line_reads: every line the METRIC grammar spells from well-
# formed parts (spec/autoresearch/metric_line.bend) means its name and a
# canonical decimal worth the value as written, when the value has at
# most 15 significant digits; nothing past that
# EXCLUDES: a misread value (sign, point, leading or trailing zeros, a
# fraction dropped), a non-canonical value (two runs with one value that
# compare apart), a lost or changed name, a valid line ignored, a value
# too long for the host read anyway
law metric_line_reads:
  for +p: ArL.Parts
  for ok: {SL.ok(p) == True{} : Bool}
  SL.Means(ArL.metric(SL.line(p)), p)

# LAW metric_line_sound: every line the parser reads a metric from is one
# the METRIC grammar spells from well-formed parts
# EXCLUDES: garbage read as a metric (no blank after METRIC, an empty
# name, `1.`, `.5`, `1e3`, text after the value, a second `=`)
law metric_line_sound:
  for +s: String
  for +kv: ArL.Kv
  for got: {ArL.metric(s) == Some{kv} : Maybe<&2, ArL.Kv>}
  exs p: ArL.Parts
  {SL.line(p) == s : String} & {SL.ok(p) == True{} : Bool}

# LAW metric_print_round_trip: a canonical decimal of at most 15 digits,
# printed (as refusals print it) after `METRIC <name>=`, reads back as
# itself
# EXCLUDES: a printer that drops a zero after the point (0.05 as 0.5), a
# point at the wrong place, a lost sign, a parser that reads its own
# printer otherwise
law metric_print_round_trip:
  for +name: String
  for +d: ArD.Dec
  for okn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}
  for c: {SD.Canon(d) == True{} : Bool}
  for fit: {Nat.is_le(SL.dlen(ArD.Dec.ds(d)), 15n) == True{} : Bool}
  {ArL.metric(String.append("METRIC ", String.append(name, SCon{'=', ArD.show(d)}))) == Some{ArL.Kv{name, d}} : Maybe<&2, ArL.Kv>}

# LAW metric_line_example: anchor: lines a benchmark prints
# EXCLUDES: a parser that misses one of the cases below
law metric_line_example:
  {[ArL.metric("METRIC ms=-0012.500 "), ArL.metric("METRIC\tp.x-1=0.0050\r"), ArL.metric("METRIC ms=-0.000"), ArL.metric("METRIC ms=1."), ArL.metric("METRICms=1"), ArL.metric("METRIC ms=1 x"), ArL.metric("METRIC ms=1234567890123456"), ArL.metric("METRIC ms=1e3"), ArL.metric("total: 3")] == [Some{ArL.Kv{"ms", ArD.Dec{True{}, [1n, 2n, 5n], 1n}}}, Some{ArL.Kv{"p.x-1", ArD.Dec{False{}, [5n], 3n}}}, Some{ArL.Kv{"ms", ArD.Dec{False{}, [], 0n}}}, None{}, None{}, None{}, None{}, None{}, None{}] : List<&2, Maybe<&2, ArL.Kv>>}

def ar_pick(b: Bool, x: Maybe<&2, ArD.Dec>, y: Maybe<&2, ArD.Dec>) -> Maybe<&2, ArD.Dec>:
  match b:
    case True{}:
      x
    case False{}:
      y

# LAW metric_last_wins: after a metric line sets name n to d, the run's
# value of n is d, and every other name keeps its value
# EXCLUDES: the first value kept, a value lost or doubled, another
# metric changed
law metric_last_wins:
  for +kvs: List<&2, ArL.Kv>
  for +n: String
  for +d: ArD.Dec
  for +x: String
  {ArS.lookup(ArS.put(kvs, n, d), x) == ar_pick(String.eq(n, x), Some{d}, ArS.lookup(kvs, x)) : Maybe<&2, ArD.Dec>}

# A run's output
# --------------

def ar_put(kvs: List<&2, ArL.Kv>, m: Maybe<&2, ArL.Kv>) -> List<&2, ArL.Kv>:
  match m:
    case None{}:
      kvs
    case Some{ArL.Kv{n, d}}:
      ArS.put(kvs, n, d)

# LAW line_sets_metric: a line of a running run's output sets the metric
# it reports, if it is a METRIC line, and changes nothing else
# EXCLUDES: a non-METRIC line that changes a metric, a metric lost, a
# line that touches another run, the configuration or the mode
law line_sets_metric:
  for +c: Maybe<&2, ArS.Cfg>
  for +seg: Nat
  for +mode: ArS.Mode
  for +runs: List<&2, ArS.Row>
  for +id: Nat
  for +kvs: List<&2, ArL.Kv>
  for +t: String
  {ArP.step(ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Line{t}) == ArS.Took{ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, ar_put(kvs, ArL.metric(t)), None{}}}}, ArS.Nothing{}, False{}} : ArS.Res}

def ar_exit_ok(neg: Bool, code: Nat, timeout: Bool) -> Bool:
  match neg:
    case True{}:
      False{}
    case False{}:
      match timeout:
        case True{}:
          False{}
        case False{}:
          Nat.is_eq(code, 0n)

# LAW finish_marks_passed: a running run that ends is finished, passed
# exactly when it exited 0 and did not time out; nothing else changes
# EXCLUDES: a timed-out or failing run marked passed, a passing run
# marked failed, metrics dropped at the end
law finish_marks_passed:
  for +c: Maybe<&2, ArS.Cfg>
  for +seg: Nat
  for +mode: ArS.Mode
  for +runs: List<&2, ArS.Row>
  for +id: Nat
  for +kvs: List<&2, ArL.Kv>
  for +neg: Bool
  for +code: Nat
  for +timeout: Bool
  {ArP.step(ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Finish{neg, code, timeout}) == ArS.Took{ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{ar_exit_ok(neg, code, timeout)}}}}, ArS.Nothing{}, False{}} : ArS.Res}

def ar_running(s: ArS.St) -> Bool:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          False{}
        case Some{ArS.Pend{id, kvs, fin}}:
          Bool.not(ar_ended(fin))

# LAW output_needs_run: with no run running, a line or an end is refused
# with exactly "autoresearch: no run is in progress"
# EXCLUDES: output read into a finished or logged run, a run finished
# twice
law output_needs_run:
  for +s: ArS.St
  for +t: String
  for +neg: Bool
  for +code: Nat
  for +timeout: Bool
  for idle: {ar_running(s) == False{} : Bool}
  {[ArP.step(s, ArS.Line{t}), ArP.step(s, ArS.Finish{neg, code, timeout})] == [ArS.Refuse{"autoresearch: no run is in progress"}, ArS.Refuse{"autoresearch: no run is in progress"}] : List<&2, ArS.Res>}

# Logs
# ----

# LAW keep_needs_pass: a keep is accepted only for a finished run that
# passed
# EXCLUDES: a crashed, timed-out or still running run kept
law keep_needs_pass:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {ar_fin(s) == Some{True{}} : Maybe<&2, Bool>}

# LAW crash_needs_failure: a crash is accepted only for a finished run
# that did not pass
# EXCLUDES: a passing run logged as a crash (its result lost)
law crash_needs_failure:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Log{ArS.Crash{}, desc, why, devs}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {ar_fin(s) == Some{False{}} : Maybe<&2, Bool>}

# LAW checks_need_pass: checks_failed is accepted only for a finished run
# that passed
# EXCLUDES: a crashed run logged as checks_failed
law checks_need_pass:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Log{ArS.Checks{}, desc, why, devs}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {ar_fin(s) == Some{True{}} : Maybe<&2, Bool>}

def ar_log_refusal(s: ArS.St) -> String:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          "autoresearch.log: no run to log; call autoresearch.run() first"
        case Some{p}:
          "autoresearch.log: the run has not finished"

# LAW log_needs_pending: with no finished pending run, every log is
# refused with exactly the text that says why (no run, or it still runs)
# EXCLUDES: a log with nothing to log, a running run logged, another
# refusal text
law log_needs_pending:
  for +s: ArS.St
  for +st: ArS.Status
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for no: {ar_fin(s) == None{} : Maybe<&2, Bool>}
  {ArP.step(s, ArS.Log{st, desc, why, devs}) == ArS.Refuse{ar_log_refusal(s)} : ArS.Res}

def ar_keep_beats.m(m: Maybe<&2, ArD.Dec>, +dir: ArS.Dir, runs: List<&2, ArS.Row>, +seg: Nat) -> Type:
  match m:
    case None{}:
      Empty
    case Some{+x}:
      {SG.all_beaten(~ArD.Dec.cmp, dir, x, runs, seg) == True{} : Bool}

# the pending run has the primary metric, and it beats every kept run of
# the segment that is not flagged
def ar_keep_beats(s: ArS.St) -> Type:
  match s:
    case ArS.St{cfg, +seg, mode, runs, pend}:
      match cfg:
        case None{}:
          Empty
        case Some{+c}:
          match pend:
            case None{}:
              Empty
            case Some{ArS.Pend{id, kvs, fin}}:
              ar_keep_beats.m(ArS.lookup(kvs, ArS.Cfg.metric(c)), ArS.Cfg.dir(c), runs, seg)

# LAW keep_is_better: a keep is accepted only when the run printed the
# primary metric and it is strictly better (in the configured direction)
# than every kept run of the segment that is not flagged; the first keep
# of a segment (its baseline) beats none
# EXCLUDES: a keep that ties or loses to the best, a keep with no metric,
# a keep that compares with another segment's runs or with flagged ones,
# a direction reversed
law keep_is_better:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Took{s2, eff, stop} : ArS.Res}
  ar_keep_beats(s)

def ar_justified(w: Maybe<&2, String>) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{t}:
      SL.nonempty(t)

# LAW keep_needs_justification: a keep whose run changed paths outside
# the scope is accepted only with a non-empty justification
# EXCLUDES: an out-of-scope change kept silently
law keep_needs_justification:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {Bool.or(Nat.is_eq(devs, 0n), ar_justified(why)) == True{} : Bool}

def ar_logged(s: ArS.St, st: ArS.Status, desc: String, s2: ArS.St) -> Type:
  match s:
    case ArS.St{+c, +seg, mode, runs, pend}:
      match pend:
        case None{}:
          Empty
        case Some{p}:
          {ar_runs(s2) == ArS.snoc(runs, [ar_row(c, seg, p, Some{st}, desc)]) : List<&2, ArS.Row>} & {ar_pend(s2) == None{} : Maybe<&2, ArS.Pend>} & {ar_cfg(s2) == c : Maybe<&2, ArS.Cfg>} & {ar_seg(s2) == seg : Nat}

# LAW log_records: an accepted log appends the pending run's row with the
# status and description, and its metric is the primary metric its
# output printed (the model never supplies it); no run is pending after
# it; the configuration and segment stay
# EXCLUDES: a model-supplied metric logged, a lost or rewritten earlier
# row, a run still pending after its log, a log that moves the segment
law log_records:
  for +s: ArS.St
  for +st: ArS.Status
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Log{st, desc, why, devs}) == ArS.Took{s2, eff, stop} : ArS.Res}
  ar_logged(s, st, desc, s2)

# the step accepted the log of the pending run with status st and effect
# eff, its row appended as log_records says
def ar_accepts(+s: ArS.St, st: ArS.Status, desc: String, r: ArS.Res, eff: ArS.Eff) -> Type:
  match r:
    case ArS.Took{s2, e, stop}:
      {e == eff : ArS.Eff} & ar_logged(s, st, desc, s2)
    case ArS.Refuse{t}:
      Empty

# LAW keep_accepted: a keep is accepted, commits and appends the run kept
# whenever the pending run finished and passed, printed the primary
# metric, that metric is strictly better (configured direction) than
# every kept run of the segment that is not flagged (spec/autoresearch/
# segment.bend all_beaten: with best_is_best, better than the best, or
# nothing kept yet), and it left the scope 0 times or has a non-empty
# justification. The converse of keep_needs_pass, keep_is_better and
# keep_needs_justification
# EXCLUDES: a keep refused against a flagged run or another segment's, a
# good keep refused (a stricter or reversed order, a justification asked
# for with no deviation), a keep accepted with another effect or row
law keep_accepted:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for fin: {ar_fin(s) == Some{True{}} : Maybe<&2, Bool>}
  for beats: ar_keep_beats(s)
  for just: {Bool.or(Nat.is_eq(devs, 0n), ar_justified(why)) == True{} : Bool}
  ar_accepts(s, ArS.Keep{}, desc, ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}), ArS.Commit{})

# a log other than a keep is allowed for a finished run: discard always,
# crash when it did not pass, checks_failed when it passed
def ar_log_allowed(fin: Maybe<&2, Bool>, st: ArS.Status) -> Bool:
  match fin:
    case None{}:
      False{}
    case Some{p}:
      match st:
        case ArS.Keep{}:
          False{}
        case ArS.Discard{}:
          True{}
        case ArS.Crash{}:
          Bool.not(p)
        case ArS.Checks{}:
          p

# LAW log_accepted: discard, crash and checks_failed are accepted, reset
# the tree and append the run whenever ar_log_allowed. The converse of
# crash_needs_failure and checks_need_pass
# EXCLUDES: a discard refused, a failed run that cannot be logged a
# crash, a passing run refused checks_failed, one of these accepted with
# another effect or row
law log_accepted:
  for +s: ArS.St
  for +st: ArS.Status
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for ok: {ar_log_allowed(ar_fin(s), st) == True{} : Bool}
  ar_accepts(s, st, desc, ArP.step(s, ArS.Log{st, desc, why, devs}), ArS.Reset{})

def ar_effect(e: ArS.Ev) -> ArS.Eff:
  match e:
    case ArS.Init{c, f, h}:
      ArS.Nothing{}
    case ArS.Begin{n}:
      ArS.Nothing{}
    case ArS.Line{t}:
      ArS.Nothing{}
    case ArS.Finish{n, c, t}:
      ArS.Nothing{}
    case ArS.Log{st, d, w, v}:
      match st:
        case ArS.Keep{}:
          ArS.Commit{}
        case ArS.Discard{}:
          ArS.Reset{}
        case ArS.Crash{}:
          ArS.Reset{}
        case ArS.Checks{}:
          ArS.Reset{}
    case ArS.Flag{n, r}:
      ArS.Nothing{}
    case ArS.SetMode{m}:
      ArS.Nothing{}

# LAW effect_matches_status: an accepted keep commits, every other
# accepted log resets the tree, and no other event touches it
# EXCLUDES: a discarded run's changes committed, a kept run reset, a
# start or a flag that commits or resets
law effect_matches_status:
  for +s: ArS.St
  for +e: ArS.Ev
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}
  {eff == ar_effect(e) : ArS.Eff}

def ar_capped.max(m: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      Nat.is_le(k, n)

# the configuration caps a segment at n logged runs or fewer
def ar_capped(c: Maybe<&2, ArS.Cfg>, +n: Nat) -> Bool:
  match c:
    case None{}:
      False{}
    case Some{k}:
      ar_capped.max(ArS.Cfg.max(k), n)

def ar_mode_after(e: ArS.Ev, stop: Bool, mode: ArS.Mode) -> ArS.Mode:
  match e:
    case ArS.Init{c, f, h}:
      ArS.On{}
    case ArS.Begin{n}:
      mode
    case ArS.Line{t}:
      mode
    case ArS.Finish{n, c, t}:
      mode
    case ArS.Log{st, d, w, v}:
      match stop:
        case True{}:
          ArS.Off{}
        case False{}:
          mode
    case ArS.Flag{n, r}:
      mode
    case ArS.SetMode{m}:
      m

# LAW cap_stops: an accepted step stops exactly when it is a log after
# which the segment logged at least max_iterations runs; a stop sets the
# mode Off, an init sets it On, the mode event sets it, nothing else
# changes it
# EXCLUDES: a loop that runs past its cap, a stop before it, a stop that
# leaves the mode On, a mode changed by a start or a line
law cap_stops:
  for +s: ArS.St
  for +e: ArS.Ev
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}
  {stop == Bool.and(ar_is_log(e), ar_capped(ar_cfg(s2), ArS.St.logged(s2))) : Bool} & {ar_mode(s2) == ar_mode_after(e, stop, ar_mode(s)) : ArS.Mode}

# Starts, inits, segments
# -----------------------

# LAW start_abandons: an accepted start has the next run's id; the run it
# starts is the only pending one, with no metrics; the pending run before
# it, if any, ends as an abandoned row (no status); nothing else changes
# EXCLUDES: two pending runs, a lost pending run, a reused or skipped id,
# a start that keeps the old run's metrics
law start_abandons:
  for +s: ArS.St
  for +n: Nat
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Begin{n}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {n == 1n+ar_started(s) : Nat} & {s2 == ArS.St{ar_cfg(s), ar_seg(s), ar_mode(s), ArS.snoc(ar_runs(s), ar_gone(s)), Some{ArS.Pend{n, Nil{}, None{}}}} : ArS.St}

def ar_no_cfg(s: ArS.St) -> Bool:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match c:
        case None{}:
          True{}
        case Some{k}:
          False{}

# LAW init_needs_harness: a first init, or one that opens a new segment,
# is accepted only when the benchmark harness exists
# EXCLUDES: an experiment started with nothing to measure
law init_needs_harness:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +fresh: Bool
  for +harness: Bool
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Init{c, fresh, harness}) == ArS.Took{s2, eff, stop} : ArS.Res}
  for new: {Bool.or(ar_no_cfg(s), fresh) == True{} : Bool}
  {harness == True{} : Bool}

def ar_cap_ok(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{n}:
      Nat.is_ne(n, 0n)

def ar_bump(s: ArS.St, e: ArS.Ev) -> Nat:
  match e:
    case ArS.Init{c, f, h}:
      match f:
        case True{}:
          ar_one(Bool.not(ar_no_cfg(s)))
        case False{}:
          0n
    case ArS.Begin{n}:
      0n
    case ArS.Line{t}:
      0n
    case ArS.Finish{n, c, t}:
      0n
    case ArS.Log{st, d, w, v}:
      0n
    case ArS.Flag{n, r}:
      0n
    case ArS.SetMode{m}:
      0n

# LAW init_sets: an accepted init has a metric name a METRIC line can
# spell and a cap of at least 1; it sets the configuration and the mode
# On, abandons the pending run, and opens the next segment only for a
# new segment of an existing experiment
# EXCLUDES: a metric no line can report, a cap of 0, a pending run kept
# across an init, a segment moved without new_segment
law init_sets:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +fresh: Bool
  for +harness: Bool
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Init{c, fresh, harness}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {Bool.and(Bool.and(SL.nonempty(ArS.Cfg.metric(c)), SL.all_name(ArS.Cfg.metric(c))), ar_cap_ok(ArS.Cfg.max(c))) == True{} : Bool} & {s2 == ArS.St{Some{c}, Nat.add(ar_seg(s), ar_bump(s, ArS.Init{c, fresh, harness})), ArS.On{}, ArS.snoc(ar_runs(s), ar_gone(s)), None{}} : ArS.St}

def ar_dir_eq(a: ArS.Dir, b: ArS.Dir) -> Bool:
  match a b:
    case ArS.Lower{} ArS.Lower{}:
      True{}
    case ArS.Lower{} ArS.Higher{}:
      False{}
    case ArS.Higher{} ArS.Lower{}:
      False{}
    case ArS.Higher{} ArS.Higher{}:
      True{}

# LAW init_keeps_metric: an init on the same segment of an experiment
# keeps its primary metric and direction
# EXCLUDES: kept runs of one metric compared with runs of another; a
# direction flipped under a segment's best
law init_keeps_metric:
  for +s: ArS.St
  for +o: ArS.Cfg
  for +c: ArS.Cfg
  for +harness: Bool
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for old: {ar_cfg(s) == Some{o} : Maybe<&2, ArS.Cfg>}
  for ok: {ArP.step(s, ArS.Init{c, False{}, harness}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), ar_dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c))) == True{} : Bool}

# LAW segment_monotone: the segment never goes back: an accepted step
# keeps it, but an init with a new segment of an existing experiment,
# which adds one
# EXCLUDES: a segment reset or skipped, a segment moved by a run or a log
law segment_monotone:
  for +s: ArS.St
  for +e: ArS.Ev
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}
  {ar_seg(s2) == Nat.add(ar_seg(s), ar_bump(s, e)) : Nat}

# Flags
# -----

def ar_flagged.at(r: ArS.Row, +id: Nat) -> Bool:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      Bool.and(Nat.is_eq(i, id), fl)

# some row of rs with this id is flagged
def ar_flagged(rs: List<&2, ArS.Row>, +id: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      Bool.or(ar_flagged.at(r, id), ar_flagged(t, id))

def ar_logged_id.at(r: ArS.Row, +id: Nat) -> Bool:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      Bool.and(Nat.is_eq(i, id), ArS.has(st))

# some row of rs with this id was logged
def ar_logged_id(rs: List<&2, ArS.Row>, +id: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      Bool.or(ar_logged_id.at(r, id), ar_logged_id(t, id))

# LAW flag_monotone: a flagged run stays flagged after every accepted
# step
# EXCLUDES: a flag lost by a later log, start or init (a noisy run that
# comes back into the best)
law flag_monotone:
  for +s: ArS.St
  for +e: ArS.Ev
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for +id: Nat
  for ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}
  for was: {ar_flagged(ar_runs(s), id) == True{} : Bool}
  {ar_flagged(ar_runs(s2), id) == True{} : Bool}

# LAW flag_marks: an accepted flag has a reason and names a logged run,
# which is flagged after it
# EXCLUDES: a flag with no reason, a flag of a pending or abandoned run, a
# flag accepted and not set
law flag_marks:
  for +s: ArS.St
  for +n: Nat
  for +reason: String
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, ArS.Flag{n, reason}) == ArS.Took{s2, eff, stop} : ArS.Res}
  {Bool.and(SL.nonempty(reason), Bool.and(ar_logged_id(ar_runs(s), n), ar_flagged(ar_runs(s2), n))) == True{} : Bool}

def ar_unflag.rows(rs: List<&2, ArS.Row>) -> List<&2, ArS.Row>:
  match rs:
    case Nil{}:
      Nil{}
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> t:
      match fl:
        case True{}:
          ar_unflag.rows(t)
        case False{}:
          ArS.Row{i, sg, st, m, ms, ps, fn, False{}, desc} <> ar_unflag.rows(t)

# the state without its flagged runs
def ar_unflag(s: ArS.St) -> ArS.St:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      ArS.St{c, seg, mode, ar_unflag.rows(runs), pend}

# LAW flagged_excluded: the baseline, best and confidence of a state are
# those of the state without its flagged runs
# EXCLUDES: a flagged run that is still the baseline or the best, or
# counts in the confidence
law flagged_excluded:
  for +s: ArS.St
  {(ArS.St.baseline(s), (ArS.St.best(s), ArT.St.confidence(s))) == (ArS.St.baseline(ar_unflag(s)), (ArS.St.best(ar_unflag(s)), ArT.St.confidence(ar_unflag(s)))) : Maybe<&2, ArD.Dec> & Maybe<&2, ArD.Dec> & Maybe<&2, Nat>}

def ar_counted.at(r: ArS.Row, +seg: Nat) -> Nat:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      ar_one(Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.has(st), Bool.and(Bool.not(fl), Maybe.is_some(&2, ArD.Dec, m)))))

# how many logged runs of the segment that are not flagged have a metric
def ar_counted(rs: List<&2, ArS.Row>, +seg: Nat) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      Nat.add(ar_counted.at(r, seg), ar_counted(t, seg))

# LAW confidence_none_below_3: with fewer than 3 metrics of logged runs of
# the segment that are not flagged, there is no confidence
# EXCLUDES: a confidence from one or two samples (a MAD of almost
# nothing, a huge spurious confidence)
law confidence_none_below_3:
  for +s: ArS.St
  for few: {Nat.is_lt(ar_counted(ar_runs(s), ar_seg(s)), 3n) == True{} : Bool}
  {ArT.St.confidence(s) == None{} : Maybe<&2, Nat>}

def ar_vals.at(ok: Bool, m: Maybe<&2, ArD.Dec>, r: List<&2, ArD.Dec>) -> List<&2, ArD.Dec>:
  match ok:
    case False{}:
      r
    case True{}:
      match m:
        case None{}:
          r
        case Some{x}:
          x <> r

# the metrics of the segment's logged runs that are not flagged, oldest
# first
def ar_vals(rs: List<&2, ArS.Row>, +seg: Nat) -> List<&2, ArD.Dec>:
  match rs:
    case Nil{}:
      Nil{}
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> t:
      ar_vals.at(Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.has(st), Bool.not(fl))), m, ar_vals(t, seg))

def ar_mwf(m: Maybe<&2, ArD.Dec>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      SD.Wf(d)

# every row's metric is well formed (as every parsed metric is:
# metric_line_reads)
def ar_rows_wf(rs: List<&2, ArS.Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> t:
      Bool.and(ar_mwf(m), ar_rows_wf(t))

# LAW confidence_exact: with well-formed metrics, the confidence is the
# spec's (spec/autoresearch/stats.bend): |best - baseline| / MAD of the
# segment's logged metrics that are not flagged, in tenths rounded down,
# at most 999999999; none below 3 metrics, without a baseline, with best
# worth the baseline or a MAD of 0
# EXCLUDES: a median of the wrong middle (even counts), a MAD over the
# metrics instead of their deviations, a sign lost in a deviation, a
# scale mixed up between metrics, a rounded or overflowed quotient, a
# flagged or other segment's metric counted
law confidence_exact:
  for +s: ArS.St
  for wf: {ar_rows_wf(ar_runs(s)) == True{} : Bool}
  {ArT.St.confidence(s) == SS.confidence(ar_vals(ar_runs(s), ar_seg(s)), ArS.St.baseline(s), ArS.St.best(s)) : Maybe<&2, Nat>}

# The whole step
# --------------

# LAW step_refines_spec: every event on every state answers exactly what
# spec/autoresearch/step.bend restates from the requirements: the same
# refusal text, or the same state, effect and stop. The METRIC parser,
# the order and the printer of metrics are the shipped ones, which
# metric_line_*, metric_order_* and metric_print_round_trip pin
# EXCLUDES: a step off the requirements in either direction: an accepted
# step refused (a start while a run is pending), a refused step accepted,
# another refusal text, another state, effect or stop
law step_refines_spec:
  for +s: ArS.St
  for +e: ArS.Ev
  {ArP.step(s, e) == SP.step(~ArD.Dec.cmp, ~ArL.metric, ~ArD.show, s, e) : ArS.Res}
