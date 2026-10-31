# eukhe: the laws of area autoresearch: the segment's best and the runs
# over histories (bend/autoresearch/). A history is a list of events
# stepped from the empty state, as the host replays its event log; the
# terms are those of laws/autoresearch/model.bend.

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../spec/autoresearch/segment.bend as SG
import ./model.bend as ArM

# Runs
# ----

def ar_starts.go(evs: List<&2, ArS.Ev>, +s: ArS.St) -> Nat:
  match evs:
    case Nil{}:
      0n
    case +e <> t:
      Nat.add(ArM.ar_one(Bool.and(ArM.ar_is_begin(e), ArM.ar_took(ArP.step(s, e)))), ar_starts.go(t, ArM.ar_after(ArP.step(s, e), s)))

# how many starts of evs were accepted, from the empty state
def ar_starts(evs: List<&2, ArS.Ev>) -> Nat:
  ar_starts.go(evs, ArS.St.empty())

def ar_ids.rows(rs: List<&2, ArS.Row>, tail: List<&2, Nat>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      tail
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> t:
      i <> ar_ids.rows(t, tail)

# the ids of every run, oldest first: the ended ones, then the pending one
def ar_ids(s: ArS.St) -> List<&2, Nat>:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          ar_ids.rows(runs, Nil{})
        case Some{ArS.Pend{id, kvs, fin}}:
          ar_ids.rows(runs, [id])

def ar_upto.go(n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n++k:
      ar_upto.go(k, (1n+k) <> acc)

# 1, 2, ..., n
def ar_upto(n: Nat) -> List<&2, Nat>:
  ar_upto.go(n, Nil{})

# how many rows are logged (logged: True) or abandoned (False)
def ar_status_n(rs: List<&2, ArS.Row>, +logged: Bool) -> Nat:
  match rs:
    case Nil{}:
      0n
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> t:
      Nat.add(ArM.ar_one(Bool.not(Bool.xor(ArS.has(st), logged))), ar_status_n(t, logged))

def ar_pending_n(s: ArS.St) -> Nat:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          0n
        case Some{p}:
          1n

# LAW run_conservation: after any history from the empty state, the runs
# (ended ones oldest first, then the pending one) are exactly runs 1, 2,
# ..., n for the n starts accepted: no run lost, doubled or out of order;
# and n = logged + abandoned + pending
# EXCLUDES: a run lost by an init or a start, a run logged twice, an id
# reused, a pending run counted twice
law run_conservation:
  for +evs: List<&2, ArS.Ev>
  {ar_ids(ArM.ar_run(evs)) == ar_upto(ar_starts(evs)) : List<&2, Nat>} & {Nat.add(ar_status_n(ArM.ar_runs(ArM.ar_run(evs)), True{}), Nat.add(ar_status_n(ArM.ar_runs(ArM.ar_run(evs)), False{}), ar_pending_n(ArM.ar_run(evs)))) == ar_starts(evs) : Nat}

# The best
# --------

def ar_best_ok(s: ArS.St) -> Type:
  match s:
    case ArS.St{cfg, +seg, mode, +runs, pend}:
      match cfg:
        case None{}:
          {SG.none_kept(runs, seg) == True{} : Bool}
        case Some{c}:
          SG.Best(~ArD.Dec.cmp, ArS.Cfg.dir(c), ArS.last(runs, seg), runs, seg)

# LAW best_is_best: after any history from the empty state, the
# segment's best is none exactly when it kept no run (that is not
# flagged); else it is a kept run's metric, and no kept run of the
# segment that is not flagged is better (spec/autoresearch/segment.bend)
# EXCLUDES: a best that a kept run beats (a keep that did not improve, a
# flag that left an older best behind), a best from another segment or
# a flagged run, a best with nothing kept
law best_is_best:
  for +evs: List<&2, ArS.Ev>
  ar_best_ok(ArM.ar_run(evs))

# LAW baseline_is_first: in every state (so after every history), the
# baseline is the metric of the first (oldest) kept run of the current
# segment that is not flagged, none when the current segment kept no
# such run (spec/autoresearch/segment.bend first_kept). confidence_exact
# reads the state's own baseline, so this also ties the confidence to
# the current segment
# EXCLUDES: a baseline carried over from an earlier segment (a new
# segment that keeps the old baseline, and the confidence built on it),
# a baseline from a later keep (the best, the last keep), a flagged,
# discarded, crashed or abandoned run as the baseline, a baseline with
# nothing kept in the segment
law baseline_is_first:
  for +s: ArS.St
  {ArS.St.baseline(s) == SG.first_kept(ArM.ar_runs(s), ArM.ar_seg(s)) : Maybe<&2, ArD.Dec>}

# LAW logged_is_segment: in every state (so after every history), the
# logged count (the snapshot's, and the one cap_stops reads) is the
# number of runs of the current segment that were logged (a status set;
# abandoned rows have none), flagged ones included
# (spec/autoresearch/segment.bend logged_count). With cap_stops (an
# equation for the stop), the cap is per segment: a step stops exactly
# when the current segment's logged runs reach max_iterations
# EXCLUDES: a count over every segment (a new segment that starts with
# the old segment's budget spent), abandoned runs counted, flagged runs
# left out of the cap
law logged_is_segment:
  for +s: ArS.St
  {ArS.St.logged(s) == SG.logged_count(ArM.ar_runs(s), ArM.ar_seg(s)) : Nat}

def ar_better.of(c: Maybe<&2, ArS.Cfg>, b2: Maybe<&2, ArD.Dec>, b: Maybe<&2, ArD.Dec>) -> Type:
  match c:
    case None{}:
      Empty
    case Some{k}:
      match b2:
        case None{}:
          Empty
        case Some{+x}:
          match b:
            case None{}:
              Unit
            case Some{y}:
              {SG.is_better(~ArD.Dec.cmp, ArS.Cfg.dir(k), x, y) == True{} : Bool}

# the best of s2 is the best of s, or a metric better than it (or the
# first one)
def ar_not_worse(+s: ArS.St, +s2: ArS.St) -> Type:
  {ArS.St.best(s2) == ArS.St.best(s) : Maybe<&2, ArD.Dec>} | ar_better.of(ArM.ar_cfg(s2), ArS.St.best(s2), ArS.St.best(s))

# LAW best_never_worse: within a segment, an accepted step other than a
# flag keeps the best or makes it strictly better (only a flag may drop
# a best)
# EXCLUDES: a best replaced by a worse run (a discard or crash counted, a
# keep that lost), a best lost by a start, an init or a mode change
law best_never_worse:
  for +s: ArS.St
  for +e: ArS.Ev
  for +s2: ArS.St
  for +eff: ArS.Eff
  for +stop: Bool
  for ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}
  for nf: {ArM.ar_is_flag(e) == False{} : Bool}
  for same: {ArM.ar_seg(s2) == ArM.ar_seg(s) : Nat}
  ar_not_worse(s, s2)

# An example
# ----------

# a session: init (max 4, lower is better); run 1 prints ms 10 then
# 12.50 and mem 3, keep; run 2 prints 13, discard; run 3 prints 11 and
# fails, crash; run 4 prints -0.5, keep (out of scope, justified)
def ar_session() -> List<&2, ArS.Ev>:
  [ArS.Init{ArS.Cfg{"speed", "faster", "ms", "ms", ArS.Lower{}, [], [], [], Some{4n}}, False{}, True{}}, ArS.Begin{1n}, ArS.Line{"METRIC ms=10"}, ArS.Line{"METRIC ms=12.50"}, ArS.Line{"METRIC mem=3"}, ArS.Finish{False{}, 0n, False{}}, ArS.Log{ArS.Keep{}, "a", None{}, 0n}, ArS.Begin{2n}, ArS.Line{"METRIC ms=13"}, ArS.Finish{False{}, 0n, False{}}, ArS.Log{ArS.Discard{}, "b", None{}, 0n}, ArS.Begin{3n}, ArS.Line{"METRIC ms=11"}, ArS.Finish{True{}, 1n, False{}}, ArS.Log{ArS.Crash{}, "c", None{}, 0n}, ArS.Begin{4n}, ArS.Line{"METRIC ms=-0.5"}, ArS.Finish{False{}, 0n, False{}}, ArS.Log{ArS.Keep{}, "d", Some{"moved"}, 2n}]

# the session's state; with a fifth run of 9 to log; with run 4 flagged
def ar_ex() -> ArS.St:
  ArM.ar_run(ar_session())

def ar_ex_fifth() -> ArS.St:
  ArM.ar_run(List.append(&2, ArS.Ev, ar_session(), [ArS.Begin{5n}, ArS.Line{"METRIC ms=9"}, ArS.Finish{False{}, 0n, False{}}]))

def ar_ex_flagged() -> ArS.St:
  ArM.ar_run(List.append(&2, ArS.Ev, ar_session(), [ArS.Flag{4n, "noise"}]))

# LAW autoresearch_example: anchor: the session above ends with the mode
# Off (4 runs logged), baseline 12.5, best -0.5, confidence 13.0 (median
# 11.75, MAD 1); a fifth keep of 9 is refused; flagging run 4 makes 12.5
# the best again and drops the confidence (best = baseline)
# EXCLUDES: a model that misses one of these numbers
law autoresearch_example:
  {(ArM.ar_mode(ar_ex()), ArS.St.baseline(ar_ex()), ArS.St.best(ar_ex()), ArS.St.logged(ar_ex()), ArT.St.confidence(ar_ex())) == (ArS.Off{}, Some{ArD.Dec{False{}, [1n, 2n, 5n], 1n}}, Some{ArD.Dec{True{}, [5n], 1n}}, 4n, Some{130n}) : ArS.Mode & Maybe<&2, ArD.Dec> & Maybe<&2, ArD.Dec> & Nat & Maybe<&2, Nat>} & {ArP.step(ar_ex_fifth(), ArS.Log{ArS.Keep{}, "e", None{}, 0n}) == ArS.Refuse{"autoresearch.log: 9 is not better than the best kept -0.5 (lower is better); log discard"} : ArS.Res} & {(ArS.St.best(ar_ex_flagged()), ArT.St.confidence(ar_ex_flagged())) == (Some{ArD.Dec{False{}, [1n, 2n, 5n], 1n}}, None{}) : Maybe<&2, ArD.Dec> & Maybe<&2, Nat>}

# a session over two segments (no cap, lower is better): ms 10 kept in
# segment 0; a fresh init opens segment 1; then 5, 4, 3 kept
def ar_seg_run(n: Nat, line: String) -> List<&2, ArS.Ev>:
  [ArS.Begin{n}, ArS.Line{line}, ArS.Finish{False{}, 0n, False{}}, ArS.Log{ArS.Keep{}, "k", None{}, 0n}]

def ar_seg_cfg() -> ArS.Cfg:
  ArS.Cfg{"speed", "faster", "ms", "ms", ArS.Lower{}, [], [], [], None{}}

def ar_ex_seg() -> ArS.St:
  ArM.ar_run(List.concat(&2, ArS.Ev, [[ArS.Init{ar_seg_cfg(), False{}, True{}}], ar_seg_run(1n, "METRIC ms=10"), [ArS.Init{ar_seg_cfg(), True{}, True{}}], ar_seg_run(2n, "METRIC ms=5"), ar_seg_run(3n, "METRIC ms=4"), ar_seg_run(4n, "METRIC ms=3")]))

# LAW baseline_segment_example: anchor: the session above ends in
# segment 1 with baseline 5 (the first keep of segment 1, not the 10 of
# segment 0), best 3 and confidence 2.0 (|3 - 5| / MAD 1 of 5, 4, 3)
# EXCLUDES: a baseline or confidence taken from an earlier segment
law baseline_segment_example:
  {(ArM.ar_seg(ar_ex_seg()), ArS.St.baseline(ar_ex_seg()), ArS.St.best(ar_ex_seg()), ArT.St.confidence(ar_ex_seg())) == (1n, Some{ArD.Dec{False{}, [5n], 0n}}, Some{ArD.Dec{False{}, [3n], 0n}}, Some{20n}) : Nat & Maybe<&2, ArD.Dec> & Maybe<&2, ArD.Dec> & Maybe<&2, Nat>}

# a session (no cap, lower is better): run 1 keeps 10, run 2 keeps 1 and
# is flagged as noise, run 3 passes printing 9 and waits for its log
def ar_ex_flag_keep() -> ArS.St:
  ArM.ar_run(List.concat(&2, ArS.Ev, [[ArS.Init{ar_seg_cfg(), False{}, True{}}], ar_seg_run(1n, "METRIC ms=10"), ar_seg_run(2n, "METRIC ms=1"), [ArS.Flag{2n, "noise"}, ArS.Begin{3n}, ArS.Line{"METRIC ms=9"}, ArS.Finish{False{}, 0n, False{}}]]))

# an accepted step's effect; none on a refusal
def ar_took_eff(r: ArS.Res) -> Maybe<&2, ArS.Eff>:
  match r:
    case ArS.Took{s2, e, stop}:
      Some{e}
    case ArS.Refuse{t}:
      None{}

def ar_ex_flag_keep_log() -> ArS.Res:
  ArP.step(ar_ex_flag_keep(), ArS.Log{ArS.Keep{}, "faster", None{}, 0n})

# LAW keep_after_flag_example: anchor: the session above has best 10
# (run 2 is flagged), and keeping run 3 (9) is accepted: it commits, the
# mode stays On, and 9 is the new best
# EXCLUDES: a keep checked against a flagged run (refused as "not better
# than the best kept 1")
law keep_after_flag_example:
  {(ArS.St.best(ar_ex_flag_keep()), ar_took_eff(ar_ex_flag_keep_log()), ArS.St.best(ArM.ar_after(ar_ex_flag_keep_log(), ar_ex_flag_keep())), ArM.ar_mode(ArM.ar_after(ar_ex_flag_keep_log(), ar_ex_flag_keep()))) == (Some{ArD.Dec{False{}, [1n, 0n], 0n}}, Some{ArS.Commit{}}, Some{ArD.Dec{False{}, [9n], 0n}}, ArS.On{}) : Maybe<&2, ArD.Dec> & Maybe<&2, ArS.Eff> & Maybe<&2, ArD.Dec> & ArS.Mode}

# a session capped at 2 runs a segment (lower is better): run 1 prints
# 10, discard (segment 0); a fresh init opens segment 1; run 2 prints 9
# and waits for its log
def ar_cap_cfg() -> ArS.Cfg:
  ArS.Cfg{"speed", "faster", "ms", "ms", ArS.Lower{}, [], [], [], Some{2n}}

def ar_cap_evs() -> List<&2, ArS.Ev>:
  [ArS.Init{ar_cap_cfg(), False{}, True{}}, ArS.Begin{1n}, ArS.Line{"METRIC ms=10"}, ArS.Finish{False{}, 0n, False{}}, ArS.Log{ArS.Discard{}, "a", None{}, 0n}, ArS.Init{ar_cap_cfg(), True{}, True{}}, ArS.Begin{2n}, ArS.Line{"METRIC ms=9"}, ArS.Finish{False{}, 0n, False{}}]

def ar_ex_cap() -> ArS.St:
  ArM.ar_run(ar_cap_evs())

def ar_ex_cap_log() -> ArS.Res:
  ArP.step(ar_ex_cap(), ArS.Log{ArS.Keep{}, "b", None{}, 0n})

# then run 2 kept, run 3 prints 8 and waits for its log
def ar_ex_cap2() -> ArS.St:
  ArM.ar_run(List.append(&2, ArS.Ev, ar_cap_evs(), [ArS.Log{ArS.Keep{}, "b", None{}, 0n}, ArS.Begin{3n}, ArS.Line{"METRIC ms=8"}, ArS.Finish{False{}, 0n, False{}}]))

def ar_ex_cap2_log() -> ArS.Res:
  ArP.step(ar_ex_cap2(), ArS.Log{ArS.Discard{}, "c", None{}, 0n})

# an accepted step's stop; none on a refusal
def ar_took_stop(r: ArS.Res) -> Maybe<&2, Bool>:
  match r:
    case ArS.Took{s2, e, stop}:
      Some{stop}
    case ArS.Refuse{t}:
      None{}

# LAW cap_segment_example: anchor: keeping run 2 (the first logged run
# of segment 1) commits and does not stop: the mode stays On and the
# segment logged 1 run; logging run 3 (its second) stops: mode Off,
# logged 2
# EXCLUDES: a cap counted over every segment (the first run of a new
# segment stopping the loop), a cap that never stops
law cap_segment_example:
  {(ar_took_eff(ar_ex_cap_log()), ar_took_stop(ar_ex_cap_log()), ArM.ar_mode(ArM.ar_after(ar_ex_cap_log(), ar_ex_cap())), ArS.St.logged(ArM.ar_after(ar_ex_cap_log(), ar_ex_cap())), ar_took_stop(ar_ex_cap2_log()), ArM.ar_mode(ArM.ar_after(ar_ex_cap2_log(), ar_ex_cap2())), ArS.St.logged(ArM.ar_after(ar_ex_cap2_log(), ar_ex_cap2()))) == (Some{ArS.Commit{}}, Some{False{}}, ArS.On{}, 1n, Some{True{}}, ArS.Off{}, 2n) : Maybe<&2, ArS.Eff> & Maybe<&2, Bool> & ArS.Mode & Nat & Maybe<&2, Bool> & ArS.Mode & Nat}

# a session (no cap, lower is better): run 1 starts and prints 10; it is
# still pending (not finished, not logged)
def ar_ex_pending() -> ArS.St:
  ArM.ar_run([ArS.Init{ar_seg_cfg(), False{}, True{}}, ArS.Begin{1n}, ArS.Line{"METRIC ms=10"}])

# LAW start_abandons_example: anchor: starting run 2 while run 1 is
# pending is accepted (no effect, no stop): run 1 ends as an abandoned
# row (no status, its metric 10 kept, not passed, not finished) and run 2
# is the only pending run, with no metrics
# EXCLUDES: a start refused while a run is pending (R1), a pending run
# lost instead of abandoned
law start_abandons_example:
  {ArP.step(ar_ex_pending(), ArS.Begin{2n}) == ArS.Took{ArS.St{Some{ar_seg_cfg()}, 0n, ArS.On{}, [ArS.Row{1n, 0n, None{}, Some{ArD.Dec{False{}, [1n, 0n], 0n}}, Nil{}, False{}, False{}, False{}, ""}], Some{ArS.Pend{2n, Nil{}, None{}}}}, ArS.Nothing{}, False{}} : ArS.Res}
