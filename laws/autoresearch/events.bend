# eukhe: the laws of area autoresearch: each event of the step
# (bend/autoresearch/step.bend), its refusals and what it keeps, and the
# row a run leaves after its output (requirements X1, X2, A4-A9 of
# laws/autoresearch/model.bend). A refusal is stated with its exact text:
# the text tells the model what to do instead. What an accepted step
# leaves is stated by observations of the state (the configuration, the
# rows, the pending run), never by the code's own state equation; the
# segment, effect, stop and mode of every accepted step are those of
# segment_monotone, effect_matches_status and cap_stops.

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/metric_line.bend as SL
import ../../spec/autoresearch/segment.bend as SG
import ./model.bend as ArM
import ./history.bend as ArH

# Terms
# -----

# a row's id, segment, status, passed, finished, flagged and description
def ar_head(r: ArS.Row) -> Nat & Nat & Maybe<&2, ArS.Status> & Bool & Bool & Bool & String:
  match r:
    case ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      (id, sg, st, ps, fn, fl, desc)

# rs2 is the rows of s, then the row the pending run of s leaves when it
# is abandoned: none without a pending run; else one row, after the
# others, with its id, the segment, no status, passed and finished as its
# end said (not passed, not finished when it did not end), not flagged
# and no description (its metrics: run_row_is_its_output)
def ar_abandons(s: ArS.St, rs2: List<&2, ArS.Row>) -> Type:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          {rs2 == runs : List<&2, ArS.Row>}
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, +fin}:
              &r: ArS.Row -> ({rs2 == List.append(&2, ArS.Row, runs, [r]) : List<&2, ArS.Row>} & {ar_head(r) == (id, seg, None{}, ArM.ar_passed(fin), ArM.ar_ended(fin), False{}, "") : Nat & Nat & Maybe<&2, ArS.Status> & Bool & Bool & Bool & String})

# the id of the pending run, if any
def ar_pend_id(s: ArS.St) -> Maybe<&2, Nat>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          None{}
        case Some{ArS.Pend{id, kvs, fin}}:
          Some{id}

# the metrics the pending run printed so far, if there is one
def ar_pend_kvs(s: ArS.St) -> Maybe<&2, List<&2, ArL.Kv>>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          None{}
        case Some{ArS.Pend{id, kvs, fin}}:
          Some{kvs}

# the pending run's value of the primary metric (none without a
# configuration or a pending run)
def ar_pmetric(s: ArS.St) -> Maybe<&2, ArD.Dec>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          None{}
        case Some{ArS.Pend{id, kvs, fin}}:
          ArS.lookup(kvs, ArM.ar_name(c))

# the metric's name is one a METRIC line can carry: the name clause of
# the METRIC grammar (spec/autoresearch/metric_line.bend SL.ok)
def ar_name_ok(+n: String) -> Bool:
  Bool.and(SL.nonempty(n), SL.all_name(n))

# a run passed: it exited 0 and was not killed by its timeout (oh-my-pi
# run-experiment.ts: `passed = execution.exitCode === 0 &&
# !execution.killed`); the exit code is its sign and size
def ar_exit_passed(neg: Bool, code: Nat, timeout: Bool) -> Bool:
  match code:
    case 0n:
      Bool.and(Bool.not(neg), Bool.not(timeout))
    case 1n+k:
      False{}

# the rows rs with every flag cleared
def ar_unmark(rs: List<&2, ArS.Row>) -> List<&2, ArS.Row>:
  match rs:
    case Nil{}:
      Nil{}
    case ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc} <> t:
      ArS.Row{id, sg, st, m, ms, ps, fn, False{}, desc} <> ar_unmark(t)

# the word of a direction, and the best a refused keep names
def ar_dir_word(d: ArS.Dir) -> String:
  match d:
    case ArS.Lower{}:
      "lower"
    case ArS.Higher{}:
      "higher"

def ar_best_text(b: Maybe<&2, ArD.Dec>) -> String:
  match b:
    case None{}:
      "none"
    case Some{x}:
      ArD.show(x)

# Output: what a run printed
# --------------------------

def ar_lines(ts: List<&2, String>) -> List<&2, ArS.Ev>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      ArS.Line{t} <> ar_lines(rest)

def ar_value_hit(hit: Bool, d: ArD.Dec, acc: Maybe<&2, ArD.Dec>) -> Maybe<&2, ArD.Dec>:
  match hit:
    case True{}:
      Some{d}
    case False{}:
      acc

def ar_value_at(m: Maybe<&2, ArL.Kv>, +x: String, acc: Maybe<&2, ArD.Dec>) -> Maybe<&2, ArD.Dec>:
  match m:
    case None{}:
      acc
    case Some{ArL.Kv{n, d}}:
      ar_value_hit(String.eq(n, x), d, acc)

# the value of name x the lines ts print last, after acc: the parser's
# (ArL.metric, pinned by metric_line_reads and metric_line_sound) value of
# the last line read as a metric named x; acc when no line is
def ar_last_value(ts: List<&2, String>, +x: String, acc: Maybe<&2, ArD.Dec>) -> Maybe<&2, ArD.Dec>:
  match ts:
    case Nil{}:
      acc
    case t <> rest:
      ar_last_value(rest, x, ar_value_at(ArL.metric(t), x, acc))

def ar_mlist(m: Maybe<&2, ArD.Dec>) -> List<&2, ArD.Dec>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      [d]

def ar_binds.at(hit: Bool, v: ArD.Dec, r: List<&2, ArD.Dec>) -> List<&2, ArD.Dec>:
  match hit:
    case True{}:
      v <> r
    case False{}:
      r

# every value kvs holds for name x, in order
def ar_binds(kvs: List<&2, ArL.Kv>, +x: String) -> List<&2, ArD.Dec>:
  match kvs:
    case Nil{}:
      Nil{}
    case ArL.Kv{k, v} <> t:
      ar_binds.at(String.eq(k, x), v, ar_binds(t, x))

# what a row's other metrics hold for name x: nothing for the primary
# metric m, else the last value of x the lines print (nothing when none)
def ar_others.at(prim: Bool, +x: String, ts: List<&2, String>) -> List<&2, ArD.Dec>:
  match prim:
    case True{}:
      Nil{}
    case False{}:
      ar_mlist(ar_last_value(ts, x, None{}))

def ar_others(m: String, +x: String, ts: List<&2, String>) -> List<&2, ArD.Dec>:
  ar_others.at(String.eq(m, x), x, ts)

# r is run n of segment g, ended with status st (none: abandoned),
# passed p, finished f and description desc, after its output printed the
# lines ts: not flagged; its metric is the last value of the primary
# metric m the lines print; its other metrics hold, for every name, just
# the last value printed, and nothing for m
def ar_row_is(r: ArS.Row, +n: Nat, +g: Nat, st: Maybe<&2, ArS.Status>, p: Bool, f: Bool, desc: String, +m: String, +ts: List<&2, String>) -> Type:
  match r:
    case ArS.Row{id, sg, st2, met, ms, ps, fn, fl, d2}:
      {(id, sg, st2, ps, fn, fl, d2) == (n, g, st, p, f, False{}, desc) : Nat & Nat & Maybe<&2, ArS.Status> & Bool & Bool & Bool & String} & ({met == ar_last_value(ts, m, None{}) : Maybe<&2, ArD.Dec>} & (@x: String -> {ar_binds(ms, x) == ar_others(m, x, ts) : List<&2, ArD.Dec>}))

# the events between a run's output and its log: none, or its end
def ar_mid_ok(mid: List<&2, ArS.Ev>) -> Bool:
  match mid:
    case Nil{}:
      True{}
    case e <> rest:
      match e:
        case ArS.Init{c, f, h}:
          False{}
        case ArS.Begin{n}:
          False{}
        case ArS.Line{t}:
          False{}
        case ArS.Finish{n, c, t}:
          match rest:
            case Nil{}:
              True{}
            case e2 <> r2:
              False{}
        case ArS.Log{st, d, w, v}:
          False{}
        case ArS.Flag{n, r}:
          False{}
        case ArS.SetMode{m}:
          False{}

# whether the run passed and finished after mid
def ar_mid_passed(mid: List<&2, ArS.Ev>) -> Bool:
  match mid:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case ArS.Init{c, f, h}:
          False{}
        case ArS.Begin{n}:
          False{}
        case ArS.Line{t}:
          False{}
        case ArS.Finish{neg, code, timeout}:
          ar_exit_passed(neg, code, timeout)
        case ArS.Log{st, d, w, v}:
          False{}
        case ArS.Flag{n, r}:
          False{}
        case ArS.SetMode{m}:
          False{}

def ar_mid_finished(mid: List<&2, ArS.Ev>) -> Bool:
  match mid:
    case Nil{}:
      False{}
    case e <> rest:
      True{}

# the event ends the pending run: a log, or a start or an init that
# abandons it
def ar_ends_run(e: ArS.Ev) -> Bool:
  match e:
    case ArS.Init{c, f, h}:
      True{}
    case ArS.Begin{n}:
      True{}
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

# the status and description the event gives the run it ends
def ar_status_of(e: ArS.Ev) -> Maybe<&2, ArS.Status>:
  match e:
    case ArS.Init{c, f, h}:
      None{}
    case ArS.Begin{n}:
      None{}
    case ArS.Line{t}:
      None{}
    case ArS.Finish{n, c, t}:
      None{}
    case ArS.Log{st, d, w, v}:
      Some{st}
    case ArS.Flag{n, r}:
      None{}
    case ArS.SetMode{m}:
      None{}

def ar_desc_of(e: ArS.Ev) -> String:
  match e:
    case ArS.Init{c, f, h}:
      ""
    case ArS.Begin{n}:
      ""
    case ArS.Line{t}:
      ""
    case ArS.Finish{n, c, t}:
      ""
    case ArS.Log{st, d, w, v}:
      d
    case ArS.Flag{n, r}:
      ""
    case ArS.SetMode{m}:
      ""

# What accepted steps leave
# -------------------------

def ar_init_ok(+s: ArS.St, c: ArS.Cfg, r: ArS.Res) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {ArM.ar_cfg(s2) == Some{c} : Maybe<&2, ArS.Cfg>} & ({ArM.ar_pend(s2) == None{} : Maybe<&2, ArS.Pend>} & ar_abandons(s, ArM.ar_runs(s2)))
    case ArS.Refuse{t}:
      Empty

def ar_start_ok(+s: ArS.St, n: Nat, r: ArS.Res) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {ArM.ar_cfg(s2) == ArM.ar_cfg(s) : Maybe<&2, ArS.Cfg>} & ({ArM.ar_pend(s2) == Some{ArS.Pend{n, Nil{}, None{}}} : Maybe<&2, ArS.Pend>} & ar_abandons(s, ArM.ar_runs(s2)))
    case ArS.Refuse{t}:
      Empty

def ar_line_ok(+s: ArS.St, r: ArS.Res) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {ArM.ar_cfg(s2) == ArM.ar_cfg(s) : Maybe<&2, ArS.Cfg>} & ({ArM.ar_runs(s2) == ArM.ar_runs(s) : List<&2, ArS.Row>} & ({ar_pend_id(s2) == ar_pend_id(s) : Maybe<&2, Nat>} & {ArM.ar_fin(s2) == None{} : Maybe<&2, Bool>}))
    case ArS.Refuse{t}:
      Empty

def ar_finish_ok(+s: ArS.St, b: Bool, r: ArS.Res) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {ArM.ar_cfg(s2) == ArM.ar_cfg(s) : Maybe<&2, ArS.Cfg>} & ({ArM.ar_runs(s2) == ArM.ar_runs(s) : List<&2, ArS.Row>} & ({ar_pend_id(s2) == ar_pend_id(s) : Maybe<&2, Nat>} & ({ar_pend_kvs(s2) == ar_pend_kvs(s) : Maybe<&2, List<&2, ArL.Kv>>} & {ArM.ar_fin(s2) == Some{b} : Maybe<&2, Bool>})))
    case ArS.Refuse{t}:
      Empty

def ar_flag_ok(+s: ArS.St, +n: Nat, r: ArS.Res) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {ArM.ar_cfg(s2) == ArM.ar_cfg(s) : Maybe<&2, ArS.Cfg>} & ({ArM.ar_seg(s2) == ArM.ar_seg(s) : Nat} & ({ArM.ar_pend(s2) == ArM.ar_pend(s) : Maybe<&2, ArS.Pend>} & ({ar_unmark(ArM.ar_runs(s2)) == ar_unmark(ArM.ar_runs(s)) : List<&2, ArS.Row>} & (@k: Nat -> {Nat.is_eq(n, k) == False{} : Bool} -> {ArM.ar_flagged(ArM.ar_runs(s2), k) == ArM.ar_flagged(ArM.ar_runs(s), k) : Bool}))))
    case ArS.Refuse{t}:
      Empty

def ar_mode_ok(+s: ArS.St, m: ArS.Mode, r: ArS.Res) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {ArM.ar_cfg(s2) == ArM.ar_cfg(s) : Maybe<&2, ArS.Cfg>} & ({ArM.ar_seg(s2) == ArM.ar_seg(s) : Nat} & ({ArM.ar_runs(s2) == ArM.ar_runs(s) : List<&2, ArS.Row>} & ({ArM.ar_pend(s2) == ArM.ar_pend(s) : Maybe<&2, ArS.Pend>} & {ArM.ar_mode(s2) == m : ArS.Mode})))
    case ArS.Refuse{t}:
      Empty

# the configuration's kind may change: no experiment, a new segment, or
# the same metric and direction
def ar_kind_ok(s: ArS.St, fresh: Bool, +c: ArS.Cfg) -> Bool:
  match s:
    case ArS.St{old, seg, mode, runs, pend}:
      match old:
        case None{}:
          True{}
        case Some{+o}:
          Bool.or(fresh, Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), ArM.ar_dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c))))

# Init
# ----

# LAW init_name_refused: whatever the state, segment flag and harness, an
# init whose metric name is not one a METRIC line can carry (one or more
# of A-Z a-z 0-9 _ . -, the name clause of the METRIC grammar) is refused
# with exactly the text that says so. A deliberate rule of eukhe: oh-my-pi
# accepts any name
# EXCLUDES: an experiment whose primary metric no benchmark line can
# report (every keep refused afterwards), another refusal text, a name
# check after another check
law init_name_refused:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +fresh: Bool
  for +harness: Bool
  for bad: {ar_name_ok(ArS.Cfg.metric(c)) == False{} : Bool}
  {ArP.step(s, ArS.Init{c, fresh, harness}) == ArS.Refuse{"autoresearch.init: the metric's name must be letters, digits, `_`, `.` or `-`: it names the METRIC <name>=<value> line"} : ArS.Res}

# LAW init_cap_refused: an init with a METRIC name and max_iterations 0 is
# refused with exactly the text that asks for at least 1, whatever the
# state, segment flag and harness. A deliberate rule of eukhe: oh-my-pi
# reads a cap of 0 or less as no cap
# EXCLUDES: a cap of 0 taken (a loop that stops before its first run, or
# one that never stops), another refusal text
law init_cap_refused:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +fresh: Bool
  for +harness: Bool
  for name: {ar_name_ok(ArS.Cfg.metric(c)) == True{} : Bool}
  for zero: {ArS.Cfg.max(c) == Some{0n} : Maybe<&2, Nat>}
  {ArP.step(s, ArS.Init{c, fresh, harness}) == ArS.Refuse{"autoresearch.init: max_iterations must be at least 1"} : ArS.Res}

# LAW init_harness_refused: a first init (no experiment yet) or one that
# opens a new segment, with a METRIC name and a cap of at least 1 (or
# none), is refused when the harness is missing, with exactly the text
# that asks to build it first (oh-my-pi init-experiment.ts:
# requiresHarness = !existing || isNewSegmentInit)
# EXCLUDES: an experiment or a segment started with nothing to measure,
# another refusal text
law init_harness_refused:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +fresh: Bool
  for name: {ar_name_ok(ArS.Cfg.metric(c)) == True{} : Bool}
  for cap: {ArM.ar_cap_ok(ArS.Cfg.max(c)) == True{} : Bool}
  for new: {Bool.or(ArM.ar_no_cfg(s), fresh) == True{} : Bool}
  {ArP.step(s, ArS.Init{c, fresh, False{}}) == ArS.Refuse{"autoresearch.init: build the benchmark harness first (a script that exits 0 and prints METRIC <name>=<value>), run it once, then call autoresearch.init() again"} : ArS.Res}

# LAW init_kind_refused: an init on the same segment of an experiment,
# with a METRIC name and a cap of at least 1 (or none), whose metric or
# direction differs from the experiment's, is refused with exactly the
# text that asks for new_segment, whatever the harness. A deliberate rule
# of eukhe: oh-my-pi changes the metric in place
# EXCLUDES: kept runs of one metric compared with runs of another, a
# direction flipped under a segment's best, another refusal text
law init_kind_refused:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +harness: Bool
  for name: {ar_name_ok(ArS.Cfg.metric(c)) == True{} : Bool}
  for cap: {ArM.ar_cap_ok(ArS.Cfg.max(c)) == True{} : Bool}
  for kind: {ar_kind_ok(s, False{}, c) == False{} : Bool}
  {ArP.step(s, ArS.Init{c, False{}, harness}) == ArS.Refuse{"autoresearch.init: a new metric or direction needs new_segment=True: the runs so far measure something else"} : ArS.Res}

# LAW init_accepted: an init with a METRIC name, a cap of at least 1 (or
# none), the harness when it is a first init or a new segment, and the
# same metric and direction when it stays on the segment of an
# experiment, is accepted: the configuration is the new one, no run is
# pending, and the run pending before it, if any, ends as one abandoned
# row after the rows before (ar_abandons). The converse of the four init
# refusals
# EXCLUDES: a valid init refused, a pending run kept or lost across an
# init, an old configuration kept, an earlier row rewritten or dropped
law init_accepted:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +fresh: Bool
  for +harness: Bool
  for name: {ar_name_ok(ArS.Cfg.metric(c)) == True{} : Bool}
  for cap: {ArM.ar_cap_ok(ArS.Cfg.max(c)) == True{} : Bool}
  for hs: {Bool.or(harness, Bool.not(Bool.or(ArM.ar_no_cfg(s), fresh))) == True{} : Bool}
  for kind: {ar_kind_ok(s, fresh, c) == True{} : Bool}
  ar_init_ok(s, c, ArP.step(s, ArS.Init{c, fresh, harness}))

# A run starts
# ------------

# LAW start_needs_experiment: with no experiment, every start is refused
# with exactly the text that asks for autoresearch.init() first
# EXCLUDES: a run with no metric to measure, another refusal text
law start_needs_experiment:
  for +s: ArS.St
  for +n: Nat
  for no: {ArM.ar_no_cfg(s) == True{} : Bool}
  {ArP.step(s, ArS.Begin{n}) == ArS.Refuse{"autoresearch: no experiment yet; call autoresearch.init() first"} : ArS.Res}

# LAW start_wrong_id_refused: after any history from the empty state,
# with an experiment, a start of run n is refused, with exactly the text
# naming the next run k, unless n is k = 1 + the starts accepted so far
# EXCLUDES: a reused, skipped or out-of-order run id, a start accepted
# under another id than the host's run, another refusal text
law start_wrong_id_refused:
  for +evs: List<&2, ArS.Ev>
  for +n: Nat
  for has: {ArM.ar_no_cfg(ArM.ar_run(evs)) == False{} : Bool}
  for ne: {Nat.is_eq(n, 1n+ArH.ar_starts(evs)) == False{} : Bool}
  {ArP.step(ArM.ar_run(evs), ArS.Begin{n}) == ArS.Refuse{String.append("autoresearch.run: the next run is ", Nat.show(1n+ArH.ar_starts(evs)))} : ArS.Res}

# LAW start_accepted: after any history from the empty state, with an
# experiment, the start of run k = 1 + the starts accepted so far is
# accepted (also while a run is pending): the configuration stays, run k
# is the one pending run, with no output and not finished, and the run
# pending before it, if any, ends as one abandoned row after the rows
# before (ar_abandons)
# EXCLUDES: a start refused while a run is pending, two pending runs, a
# pending run lost or kept, a new run that inherits the old run's
# metrics or end, an earlier row rewritten or dropped
law start_accepted:
  for +evs: List<&2, ArS.Ev>
  for has: {ArM.ar_no_cfg(ArM.ar_run(evs)) == False{} : Bool}
  ar_start_ok(ArM.ar_run(evs), 1n+ArH.ar_starts(evs), ArP.step(ArM.ar_run(evs), ArS.Begin{1n+ArH.ar_starts(evs)}))

# Its output and end
# ------------------

# LAW output_frame: a line of a running run's output is accepted; the
# configuration and every ended row stay, and the run stays the pending
# one (its id kept), not finished (its metrics: run_row_is_its_output)
# EXCLUDES: a line refused while the run runs, a line that ends the run,
# moves it, or touches an ended row or the configuration
law output_frame:
  for +s: ArS.St
  for +t: String
  for run: {ArM.ar_running(s) == True{} : Bool}
  ar_line_ok(s, ArP.step(s, ArS.Line{t}))

# LAW finish_records_exit: the end of a running run is accepted; the
# configuration, every ended row, the run's id and the metrics it printed
# stay, and it is finished, passed exactly when it exited 0 and was not
# killed by its timeout (oh-my-pi run-experiment.ts)
# EXCLUDES: a timed-out, failing or signalled run marked passed, a run
# that exited 0 marked failed, metrics dropped at the end, an end that
# logs or drops the run
law finish_records_exit:
  for +s: ArS.St
  for +neg: Bool
  for +code: Nat
  for +timeout: Bool
  for run: {ArM.ar_running(s) == True{} : Bool}
  ar_finish_ok(s, ar_exit_passed(neg, code, timeout), ArP.step(s, ArS.Finish{neg, code, timeout}))

def ar_ex_running() -> ArS.St:
  ArS.St{Some{ArS.Cfg{"n", "g", "ms", "", ArS.Lower{}, [], [], [], None{}}}, 0n, ArS.On{}, [], Some{ArS.Pend{1n, [], None{}}}}

def ar_ex_end(neg: Bool, code: Nat, timeout: Bool) -> Maybe<&2, Bool>:
  ArM.ar_fin(ArM.ar_after(ArP.step(ar_ex_running(), ArS.Finish{neg, code, timeout}), ar_ex_running()))

# LAW finish_exit_example: anchor: oh-my-pi's verdicts on a run's end:
# exit 0 passes; exit 1, exit -1, exit 0 killed by the timeout and exit
# 124 killed by the timeout fail
# EXCLUDES: an exit test that misses one of these cases
law finish_exit_example:
  {[ar_ex_end(False{}, 0n, False{}), ar_ex_end(False{}, 1n, False{}), ar_ex_end(True{}, 1n, False{}), ar_ex_end(False{}, 0n, True{}), ar_ex_end(False{}, 124n, True{})] == [Some{True{}}, Some{False{}}, Some{False{}}, Some{False{}}, Some{False{}}] : List<&2, Maybe<&2, Bool>>}

# LAW run_row_is_its_output: from any state, after run n starts (an
# accepted start), its output lines ts (each one reaches the running
# run), then either nothing or its end, and then an accepted log, start
# or init that ends it, the rows are the rows after the start, then one
# row: run n of the segment, with the log's status and description (none
# and "" when abandoned), passed and finished as the end said (not when it
# did not end), not flagged; its metric is the value of the primary metric
# (the experiment's at the start) that the last METRIC line of that name
# printed, read by the parser (ArL.metric), and its other metrics hold,
# for every name, just the last value printed (oh-my-pi
# parseMetricLines: Map.set). This is X2's "the logged metric is the
# parsed one"
# EXCLUDES: a model-supplied or stale metric logged, the first value kept
# instead of the last, a value of another name, a metric dropped or
# doubled, a line of another run counted, the primary metric listed among
# the others, the wrong id, status, description or end recorded, an
# earlier row rewritten
law run_row_is_its_output:
  for +s: ArS.St
  for +n: Nat
  for +ts: List<&2, String>
  for +mid: List<&2, ArS.Ev>
  for +e: ArS.Ev
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for began: {ArM.ar_took(ArP.step(s, ArS.Begin{n})) == True{} : Bool}
  for fin: {ar_mid_ok(mid) == True{} : Bool}
  for ends: {ar_ends_run(e) == True{} : Bool}
  for ok: {ArP.step(ArM.ar_run.go(List.append(&2, ArS.Ev, ar_lines(ts), mid), ArM.ar_after(ArP.step(s, ArS.Begin{n}), s)), e) == ArS.Took{s2, eff, stop} : ArS.Res}
  exs r: ArS.Row
  {ArM.ar_runs(s2) == List.append(&2, ArS.Row, ArM.ar_runs(ArM.ar_after(ArP.step(s, ArS.Begin{n}), s)), [r]) : List<&2, ArS.Row>} & ar_row_is(r, n, ArM.ar_seg(s), ar_status_of(e), ar_mid_passed(mid), ar_mid_finished(mid), ar_desc_of(e), ArM.ar_name(ArM.ar_cfg(s)), ts)

# Logs
# ----

# LAW keep_failed_refused: a keep of a finished run that failed is
# refused with exactly the text that offers crash or discard
# EXCLUDES: a failed run kept, another refusal text
law keep_failed_refused:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for failed: {ArM.ar_fin(s) == Some{False{}} : Maybe<&2, Bool>}
  {ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{"autoresearch.log: the run failed (a non-zero exit or a timeout), so it cannot be kept; log crash or discard"} : ArS.Res}

# LAW keep_no_metric_refused: a keep of a finished run that passed but
# printed no value of the primary metric is refused with exactly the text
# naming that metric
# EXCLUDES: a keep with no metric (a baseline of nothing), another text
law keep_no_metric_refused:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for passed: {ArM.ar_fin(s) == Some{True{}} : Maybe<&2, Bool>}
  for cfg: {ArM.ar_cfg(s) == Some{c} : Maybe<&2, ArS.Cfg>}
  for none: {ar_pmetric(s) == None{} : Maybe<&2, ArD.Dec>}
  {ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{String.append("autoresearch.log: the run printed no METRIC ", String.append(ArS.Cfg.metric(c), "=<value> line, so it cannot be kept; fix the harness, or log discard"))} : ArS.Res}

# LAW keep_worse_refused: a keep of a finished run that passed and printed
# the primary metric x, where x is not strictly better (configured
# direction) than every kept run of the segment that is not flagged, is
# refused with exactly the text naming x, the best the snapshot shows
# (none when there is none) and the direction, both printed as
# metric_print_canonical says
# EXCLUDES: a keep that ties or loses kept, another number or best named,
# the direction misnamed
law keep_worse_refused:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +x: ArD.Dec
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for passed: {ArM.ar_fin(s) == Some{True{}} : Maybe<&2, Bool>}
  for cfg: {ArM.ar_cfg(s) == Some{c} : Maybe<&2, ArS.Cfg>}
  for got: {ar_pmetric(s) == Some{x} : Maybe<&2, ArD.Dec>}
  for worse: {SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c), x, ArM.ar_runs(s), ArM.ar_seg(s)) == False{} : Bool}
  {ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{String.append("autoresearch.log: ", String.append(ArD.show(x), String.append(" is not better than the best kept ", String.append(ar_best_text(ArS.St.best(s)), String.append(" (", String.append(ar_dir_word(ArS.Cfg.dir(c)), " is better); log discard"))))))} : ArS.Res}

# LAW keep_unjustified_refused: a keep of a finished run that passed and
# printed a primary metric strictly better than every kept run of the
# segment (not flagged), whose run left the scope (devs above 0) with no
# non-empty justification, is refused with exactly the text asking for
# one
# EXCLUDES: an out-of-scope change kept silently, another refusal text
law keep_unjustified_refused:
  for +s: ArS.St
  for +c: ArS.Cfg
  for +x: ArD.Dec
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for passed: {ArM.ar_fin(s) == Some{True{}} : Maybe<&2, Bool>}
  for cfg: {ArM.ar_cfg(s) == Some{c} : Maybe<&2, ArS.Cfg>}
  for got: {ar_pmetric(s) == Some{x} : Maybe<&2, ArD.Dec>}
  for better: {SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c), x, ArM.ar_runs(s), ArM.ar_seg(s)) == True{} : Bool}
  for left: {Bool.or(Nat.is_eq(devs, 0n), ArM.ar_justified(why)) == False{} : Bool}
  {ArP.step(s, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{"autoresearch.log: the run changed files outside the scope; a keep needs a justification"} : ArS.Res}

# LAW crash_passed_refused: a crash of a finished run that passed is
# refused with exactly the text that offers keep, discard or
# checks_failed
# EXCLUDES: a passing run logged as a crash, another refusal text
law crash_passed_refused:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for passed: {ArM.ar_fin(s) == Some{True{}} : Maybe<&2, Bool>}
  {ArP.step(s, ArS.Log{ArS.Crash{}, desc, why, devs}) == ArS.Refuse{"autoresearch.log: the run passed; log keep, discard or checks_failed"} : ArS.Res}

# LAW checks_failed_refused: checks_failed of a finished run that failed
# is refused with exactly the text that offers crash or discard
# EXCLUDES: a crashed run logged as checks_failed, another refusal text
law checks_failed_refused:
  for +s: ArS.St
  for +desc: String
  for +why: Maybe<&2, String>
  for +devs: Nat
  for failed: {ArM.ar_fin(s) == Some{False{}} : Maybe<&2, Bool>}
  {ArP.step(s, ArS.Log{ArS.Checks{}, desc, why, devs}) == ArS.Refuse{"autoresearch.log: the run failed; log crash or discard"} : ArS.Res}

# Rows
# ----

# LAW rows_kept: an accepted step other than a flag never rewrites or
# drops an ended row: the rows after it are the rows before it, then the
# rows it adds
# EXCLUDES: a logged or abandoned run rewritten (its metric, status or
# description changed) or lost by a later start, line, end, log, init or
# mode change, rows reordered
law rows_kept:
  for +s: ArS.St
  for +e: ArS.Ev
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}
  for nf: {ArM.ar_is_flag(e) == False{} : Bool}
  exs ys: List<&2, ArS.Row>
  {ArM.ar_runs(s2) == List.append(&2, ArS.Row, ArM.ar_runs(s), ys) : List<&2, ArS.Row>}

# Flags and the mode
# ------------------

# LAW flag_needs_reason: a flag with an empty reason is refused with
# exactly the text that asks for one
# EXCLUDES: a run flagged with no reason, another refusal text
law flag_needs_reason:
  for +s: ArS.St
  for +n: Nat
  for +reason: String
  for empty: {SL.nonempty(reason) == False{} : Bool}
  {ArP.step(s, ArS.Flag{n, reason}) == ArS.Refuse{"autoresearch.flag: a flag needs a reason"} : ArS.Res}

# LAW flag_needs_logged: a flag with a reason of a run n that no logged
# row has (none, or only pending or abandoned) is refused with exactly
# the text naming n
# EXCLUDES: a pending or abandoned run flagged, a flag of an unknown run
# accepted, another refusal text
law flag_needs_logged:
  for +s: ArS.St
  for +n: Nat
  for +reason: String
  for some: {SL.nonempty(reason) == True{} : Bool}
  for no: {ArM.ar_logged_id(ArM.ar_runs(s), n) == False{} : Bool}
  {ArP.step(s, ArS.Flag{n, reason}) == ArS.Refuse{String.append("autoresearch.flag: there is no logged run ", Nat.show(n))} : ArS.Res}

# LAW flag_accepted: a flag with a reason of a logged run n is accepted;
# the configuration, segment and pending run stay, the rows stay but for
# their flags, and the flag of every run other than n stays (that n is
# flagged after: flag_marks)
# EXCLUDES: a valid flag refused, a flag that rewrites a row's metric,
# status or description, flags another run, or moves the pending run
law flag_accepted:
  for +s: ArS.St
  for +n: Nat
  for +reason: String
  for some: {SL.nonempty(reason) == True{} : Bool}
  for yes: {ArM.ar_logged_id(ArM.ar_runs(s), n) == True{} : Bool}
  ar_flag_ok(s, n, ArP.step(s, ArS.Flag{n, reason}))

# LAW mode_set: setting the mode is always accepted; it sets the mode and
# keeps the configuration, segment, rows and pending run
# EXCLUDES: a mode change refused, ignored, or one that drops a run
law mode_set:
  for +s: ArS.St
  for +m: ArS.Mode
  ar_mode_ok(s, m, ArP.step(s, ArS.SetMode{m}))
