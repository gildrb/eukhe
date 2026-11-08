# eukhe: lemmas for the logs of area autoresearch: a refusal is no
# accepted step, the row an accepted log appends, the code's segment
# order (kept, beats) against the spec's, and the rows without the
# flagged ones

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../../../bend/autoresearch/stats.bend as ArT
import ../../../spec/autoresearch/segment.bend as SG
import ../../../spec/autoresearch/metric_line.bend as SL
import ../../../laws/autoresearch/model.bend as Autoresearch

# Refusals
# --------

# G at an accepted step, trivial at a refusal
def ag.If(r: ArS.Res, G: Type) -> Type:
  match r:
    case ArS.Took{s, e, b}:
      G
    case ArS.Refuse{t}:
      Unit

# a refusal is no accepted step: anything follows
def ag.refused(-G: Type, -t: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, e: {ArS.Refuse{t} == ArS.Took{s2, eff, stop} : ArS.Res}) -> G:
  %e : ag.If(_, G)
  Unit{}

# G at None, trivial at Some
def ag.MIf(m: Maybe<&2, Bool>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# Some is not None: anything follows
def ag.some_none(-G: Type, -x: Bool, e: {Some{x} == None{} : Maybe<&2, Bool>}) -> G:
  %e : ag.MIf(_, G)
  Unit{}

# the state of an accepted step
def ag.res_st(r: ArS.Res) -> ArS.St:
  match r:
    case ArS.Took{s, e, b}:
      s
    case ArS.Refuse{t}:
      ArS.St.empty()

# The logged row
# --------------

def ag.some_eq(t: String) -> {ArL.some(t) == SL.nonempty(t) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, r}:
      {==}

# the code's row of a pending run is the law's
def ag.row_eq(c: Maybe<&2, ArS.Cfg>, seg: Nat, p: ArS.Pend, st: Maybe<&2, ArS.Status>, desc: String) -> {ArS.row(ArS.primary(c), seg, p, st, desc) == Autoresearch.ar_row(c, seg, p, st, desc) : ArS.Row}:
  match c:
    case None{}:
      match p:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case None{}:
              {==}
            case Some{b}:
              {==}
    case Some{k}:
      match k:
        case ArS.Cfg{name, goal, metric, unit, dir, sec, scope, off, max}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  {==}
                case Some{b}:
                  {==}

def ag.row_snoc(+runs: List<&2, ArS.Row>, +c: Maybe<&2, ArS.Cfg>, +seg: Nat, +p: ArS.Pend, +st: Maybe<&2, ArS.Status>, +desc: String) -> {ArS.snoc(runs, [ArS.row(ArS.primary(c), seg, p, st, desc)]) == ArS.snoc(runs, [Autoresearch.ar_row(c, seg, p, st, desc)]) : List<&2, ArS.Row>}:
  %ag.row_eq(c, seg, p, st, desc) : {ArS.snoc(runs, [ArS.row(ArS.primary(c), seg, p, st, desc)]) == ArS.snoc(runs, [_]) : List<&2, ArS.Row>}
  {==}

# a log the code records is the law's record
def ag.done(+c: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String, e: ArS.Eff, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.log.done(c, seg, mode, runs, p, st, desc, e) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, st, desc, s2):
  %ok : Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, st, desc, ag.res_st(_))
  (ag.row_snoc(runs, c, seg, p, Some{st}, desc), {==}, {==}, {==})

def ag.need_done(b: Bool, -text: String, +c: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.log.need(b, text, c, seg, mode, runs, p, st, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, st, desc, s2):
  match b:
    case True{}:
      ag.done(c, seg, mode, runs, p, st, desc, ArS.Reset{}, s2, eff, stop, ok)
    case False{}:
      ag.refused(Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, st, desc, s2), text, s2, eff, stop, ok)

def ag.why_done(w: Bool, +c: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.why(w, c, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2):
  match w:
    case True{}:
      ag.done(c, seg, mode, runs, p, ArS.Keep{}, desc, ArS.Commit{}, s2, eff, stop, ok)
    case False{}:
      ag.refused(Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2), ArP.t_justify(), s2, eff, stop, ok)

def ag.beats_done(b: Bool, +x: ArD.Dec, +dir: ArS.Dir, +why: Maybe<&2, String>, +devs: Nat, +c: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.beats(b, x, dir, why, devs, c, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2):
  match b:
    case True{}:
      ag.why_done(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), c, seg, mode, runs, p, desc, s2, eff, stop, ok)
    case False{}:
      ag.refused(Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2), ArP.t_worse(x, ArS.last(runs, seg), dir), s2, eff, stop, ok)

def ag.metric_done(m: Maybe<&2, ArD.Dec>, +k: ArS.Cfg, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.metric(m, k, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_logged(ArS.St{Some{k}, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2):
  match m:
    case None{}:
      ag.refused(Autoresearch.ar_logged(ArS.St{Some{k}, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2), ArP.t_no_metric(ArS.Cfg.metric(k)), s2, eff, stop, ok)
    case Some{+x}:
      ag.beats_done(ArS.beats(ArS.Cfg.dir(k), x, runs, seg), x, ArS.Cfg.dir(k), why, devs, Some{k}, seg, mode, runs, p, desc, s2, eff, stop, ok)

def ag.cfg_done(c: Maybe<&2, ArS.Cfg>, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.cfg(c, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2):
  match c:
    case None{}:
      ag.refused(Autoresearch.ar_logged(ArS.St{None{}, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2), ArP.t_no_cfg(), s2, eff, stop, ok)
    case Some{+k}:
      ag.metric_done(ArS.lookup(ArS.Pend.kvs(p), ArS.Cfg.metric(k)), k, why, devs, seg, mode, runs, p, desc, s2, eff, stop, ok)

def ag.keep_done(passed: Bool, +c: Maybe<&2, ArS.Cfg>, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep(passed, c, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2):
  match passed:
    case True{}:
      ag.cfg_done(c, why, devs, seg, mode, runs, p, desc, s2, eff, stop, ok)
    case False{}:
      ag.refused(Autoresearch.ar_logged(ArS.St{c, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, s2), ArP.t_failed_keep(), s2, eff, stop, ok)

# Accepted keeps
# --------------

# an accepted keep passed: its configuration check is accepted
def ag.keep_cfg(passed: Bool, +c: Maybe<&2, ArS.Cfg>, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep(passed, c, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> {ArP.keep.cfg(c, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}:
  match passed:
    case True{}:
      ok
    case False{}:
      ag.refused({ArP.keep.cfg(c, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}, ArP.t_failed_keep(), s2, eff, stop, ok)

def ag.why_true(w: Bool, +c: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.why(w, c, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> {w == True{} : Bool}:
  match w:
    case True{}:
      {==}
    case False{}:
      ag.refused({False{} == True{} : Bool}, ArP.t_justify(), s2, eff, stop, ok)

def ag.beats_true(b: Bool, +x: ArD.Dec, +dir: ArS.Dir, +why: Maybe<&2, String>, +devs: Nat, +c: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.beats(b, x, dir, why, devs, c, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ag.refused({False{} == True{} : Bool}, ArP.t_worse(x, ArS.last(runs, seg), dir), s2, eff, stop, ok)

def ag.beats_why(b: Bool, +x: ArD.Dec, +dir: ArS.Dir, +why: Maybe<&2, String>, +devs: Nat, +c: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.beats(b, x, dir, why, devs, c, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> {Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}:
  match b:
    case True{}:
      ag.why_true(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), c, seg, mode, runs, p, desc, s2, eff, stop, ok)
    case False{}:
      ag.refused({Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}, ArP.t_worse(x, ArS.last(runs, seg), dir), s2, eff, stop, ok)

def ag.metric_why(m: Maybe<&2, ArD.Dec>, +k: ArS.Cfg, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.metric(m, k, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> {Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}:
  match m:
    case None{}:
      ag.refused({Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}, ArP.t_no_metric(ArS.Cfg.metric(k)), s2, eff, stop, ok)
    case Some{+x}:
      ag.beats_why(ArS.beats(ArS.Cfg.dir(k), x, runs, seg), x, ArS.Cfg.dir(k), why, devs, Some{k}, seg, mode, runs, p, desc, s2, eff, stop, ok)

# an accepted keep left the scope only with a justification
def ag.cfg_why(c: Maybe<&2, ArS.Cfg>, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.cfg(c, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> {Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}:
  match c:
    case None{}:
      ag.refused({Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}, ArP.t_no_cfg(), s2, eff, stop, ok)
    case Some{+k}:
      ag.metric_why(ArS.lookup(ArS.Pend.kvs(p), ArS.Cfg.metric(k)), k, why, devs, seg, mode, runs, p, desc, s2, eff, stop, ok)

def ag.just_eq(w: Maybe<&2, String>) -> {ArP.justified(w) == Autoresearch.ar_justified(w) : Bool}:
  match w:
    case None{}:
      {==}
    case Some{t}:
      ag.some_eq(t)

# The kept runs: code and spec
# ----------------------------

# a flagged row keeps no metric
def ag.kept_flag(h: Bool, st: Maybe<&2, ArS.Status>, m: Maybe<&2, ArD.Dec>) -> {None{} == ArS.kept.of(Bool.and(h, Bool.and(ArS.kept.st(st), Bool.not(True{}))), m) : Maybe<&2, ArD.Dec>}:
  match h:
    case False{}:
      {==}
    case True{}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          match k:
            case ArS.Keep{}:
              {==}
            case ArS.Discard{}:
              {==}
            case ArS.Crash{}:
              {==}
            case ArS.Checks{}:
              {==}

def ag.kept_open(h: Bool, st: Maybe<&2, ArS.Status>, m: Maybe<&2, ArD.Dec>) -> {ArS.kept.of(Bool.and(h, Bool.and(ArS.kept.st(st), Bool.not(False{}))), m) == SG.kept.st(h, st, m) : Maybe<&2, ArD.Dec>}:
  match h:
    case False{}:
      {==}
    case True{}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          match k:
            case ArS.Keep{}:
              {==}
            case ArS.Discard{}:
              {==}
            case ArS.Crash{}:
              {==}
            case ArS.Checks{}:
              {==}

# the code's kept metric of a row is the spec's
def ag.kept_eq(r: ArS.Row, +seg: Nat) -> {ArS.kept(r, seg) == SG.kept(r, seg) : Maybe<&2, ArD.Dec>}:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      match fl:
        case True{}:
          %ag.kept_flag(Nat.is_eq(sg, seg), st, m) : {_ == None{} : Maybe<&2, ArD.Dec>}
          {==}
        case False{}:
          ag.kept_open(Nat.is_eq(sg, seg), st, m)

def ag.better_eq(dir: ArS.Dir, a: ArD.Dec, b: ArD.Dec) -> {ArS.better(dir, a, b) == SG.is_better(~ArD.Dec.cmp, dir, a, b) : Bool}:
  match dir:
    case ArS.Lower{}:
      {==}
    case ArS.Higher{}:
      {==}

def ag.at_eq(+dir: ArS.Dir, +m: ArD.Dec, k: Maybe<&2, ArD.Dec>) -> {ArS.beats.at(dir, m, k) == SG.beaten.at(~ArD.Dec.cmp, dir, m, k) : Bool}:
  match k:
    case None{}:
      {==}
    case Some{x}:
      ag.better_eq(dir, m, x)

# the code's beats is the spec's all_beaten under the shipped order
def ag.beats_eq(+dir: ArS.Dir, +m: ArD.Dec, rs: List<&2, ArS.Row>, +seg: Nat) -> {ArS.beats(dir, m, rs, seg) == SG.all_beaten(~ArD.Dec.cmp, dir, m, rs, seg) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      %ag.beats_eq(dir, m, t, seg) : {Bool.and(ArS.beats.at(dir, m, ArS.kept(r, seg)), ArS.beats(dir, m, t, seg)) == Bool.and(SG.beaten.at(~ArD.Dec.cmp, dir, m, SG.kept(r, seg)), _) : Bool}
      %ag.kept_eq(r, seg) : {Bool.and(ArS.beats.at(dir, m, ArS.kept(r, seg)), ArS.beats(dir, m, t, seg)) == Bool.and(SG.beaten.at(~ArD.Dec.cmp, dir, m, _), ArS.beats(dir, m, t, seg)) : Bool}
      %ag.at_eq(dir, m, ArS.kept(r, seg)) : {Bool.and(ArS.beats.at(dir, m, ArS.kept(r, seg)), ArS.beats(dir, m, t, seg)) == Bool.and(_, ArS.beats(dir, m, t, seg)) : Bool}
      {==}

# an accepted keep beats the segment's kept runs, as the spec says
def ag.metric_better(m: Maybe<&2, ArD.Dec>, +k: ArS.Cfg, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.metric(m, k, why, devs, seg, mode, runs, p, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_keep_beats.m(m, ArS.Cfg.dir(k), runs, seg):
  match m:
    case None{}:
      ag.refused(Empty, ArP.t_no_metric(ArS.Cfg.metric(k)), s2, eff, stop, ok)
    case Some{+x}:
      %ag.beats_eq(ArS.Cfg.dir(k), x, runs, seg) : {_ == True{} : Bool}
      ag.beats_true(ArS.beats(ArS.Cfg.dir(k), x, runs, seg), x, ArS.Cfg.dir(k), why, devs, Some{k}, seg, mode, runs, p, desc, s2, eff, stop, ok)

def ag.cfg_better(c: Maybe<&2, ArS.Cfg>, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, +kvs: List<&2, ArL.Kv>, +fin: Maybe<&2, Bool>, +desc: String, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.keep.cfg(c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc) == ArS.Took{s2, eff, stop} : ArS.Res}) -> Autoresearch.ar_keep_beats(ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, fin}}}):
  match c:
    case None{}:
      ag.refused(Empty, ArP.t_no_cfg(), s2, eff, stop, ok)
    case Some{+k}:
      ag.metric_better(ArS.lookup(kvs, ArS.Cfg.metric(k)), k, why, devs, seg, mode, runs, ArS.Pend{id, kvs, fin}, desc, s2, eff, stop, ok)

# Rows without the flagged ones
# -----------------------------

def ag.first_unflag(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArS.first(rs, seg) == ArS.first(Autoresearch.ar_unflag.rows(rs), seg) : Maybe<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          match fl:
            case True{}:
              %ag.kept_flag(Nat.is_eq(sg, seg), st, m) : {ArS.first.at(_, ArS.first(t, seg)) == ArS.first(Autoresearch.ar_unflag.rows(t), seg) : Maybe<&2, ArD.Dec>}
              ag.first_unflag(t, seg)
            case False{}:
              %ag.first_unflag(t, seg) : {ArS.first.at(ArS.kept(ArS.Row{i, sg, st, m, ms, ps, fn, False{}, desc}, seg), ArS.first(t, seg)) == ArS.first.at(ArS.kept(ArS.Row{i, sg, st, m, ms, ps, fn, False{}, desc}, seg), _) : Maybe<&2, ArD.Dec>}
              {==}

def ag.last_none(r: Maybe<&2, ArD.Dec>) -> {ArS.last.at(None{}, r) == r : Maybe<&2, ArD.Dec>}:
  match r:
    case None{}:
      {==}
    case Some{x}:
      {==}

def ag.last_unflag(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArS.last(rs, seg) == ArS.last(Autoresearch.ar_unflag.rows(rs), seg) : Maybe<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          match fl:
            case True{}:
              %ag.kept_flag(Nat.is_eq(sg, seg), st, m) : {ArS.last.at(_, ArS.last(t, seg)) == ArS.last(Autoresearch.ar_unflag.rows(t), seg) : Maybe<&2, ArD.Dec>}
              %ag.last_unflag(t, seg) : {ArS.last.at(None{}, ArS.last(t, seg)) == _ : Maybe<&2, ArD.Dec>}
              ag.last_none(ArS.last(t, seg))
            case False{}:
              %ag.last_unflag(t, seg) : {ArS.last.at(ArS.kept(ArS.Row{i, sg, st, m, ms, ps, fn, False{}, desc}, seg), ArS.last(t, seg)) == ArS.last.at(ArS.kept(ArS.Row{i, sg, st, m, ms, ps, fn, False{}, desc}, seg), _) : Maybe<&2, ArD.Dec>}
              {==}

def ag.vals_flag(a: Bool, b: Bool, m: Maybe<&2, ArD.Dec>, r: List<&2, ArD.Dec>) -> {ArT.vals.at(Bool.and(a, Bool.and(b, Bool.not(True{}))), m, r) == r : List<&2, ArD.Dec>}:
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case False{}:
          {==}
        case True{}:
          {==}

def ag.vals_unflag(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArT.vals(rs, seg) == ArT.vals(Autoresearch.ar_unflag.rows(rs), seg) : List<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          match fl:
            case True{}:
              %ag.vals_unflag(t, seg) : {ArT.vals.at(Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.has(st), Bool.not(True{}))), m, ArT.vals(t, seg)) == _ : List<&2, ArD.Dec>}
              ag.vals_flag(Nat.is_eq(sg, seg), ArS.has(st), m, ArT.vals(t, seg))
            case False{}:
              %ag.vals_unflag(t, seg) : {ArT.vals.at(Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.has(st), Bool.not(False{}))), m, ArT.vals(t, seg)) == ArT.vals.at(Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.has(st), Bool.not(False{}))), m, _) : List<&2, ArD.Dec>}
              {==}

# the view of a state a snapshot shows: baseline, best, confidence, from
# the first and last kept metric and the segment's metrics
def ag.view(+f: Maybe<&2, ArD.Dec>, +l: Maybe<&2, ArD.Dec>, +vs: List<&2, ArD.Dec>) -> Maybe<&2, ArD.Dec> & Maybe<&2, ArD.Dec> & Maybe<&2, Nat>:
  (f, (l, ArT.conf.count(Nat.is_le(3n, ArT.dlen(vs)), f, l, vs, ArT.dlen(vs))))

# Counted metrics
# ---------------

def ag.BIf(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True: anything follows
def ag.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : ag.BIf(_, G)
  Unit{}

def ag.cnt_at(a: Bool, b: Bool, f: Bool, m: Maybe<&2, ArD.Dec>, -r: List<&2, ArD.Dec>, -k: Nat, ih: {ArT.dlen(r) == k : Nat}) -> {ArT.dlen(ArT.vals.at(Bool.and(a, Bool.and(b, Bool.not(f))), m, r)) == Nat.add(Autoresearch.ar_one(Bool.and(a, Bool.and(b, Bool.and(Bool.not(f), Maybe.is_some(&2, ArD.Dec, m))))), k) : Nat}:
  match a:
    case False{}:
      ih
    case True{}:
      match b:
        case False{}:
          ih
        case True{}:
          match f:
            case True{}:
              ih
            case False{}:
              match m:
                case None{}:
                  ih
                case Some{x}:
                  %ih : {ArT.dlen(x <> r) == Nat.add(1n, _) : Nat}
                  {==}

# the segment's metrics are as many as the law counts
def ag.cnt(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArT.dlen(ArT.vals(rs, seg)) == Autoresearch.ar_counted(rs, seg) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          ag.cnt_at(Nat.is_eq(sg, seg), ArS.has(st), fl, m, ArT.vals(t, seg), Autoresearch.ar_counted(t, seg), ag.cnt(t, seg))

def ag.few(-a: Nat, -b: Nat, e: {a == b : Nat}, h: {Nat.is_lt(b, 3n) == True{} : Bool}) -> {Nat.is_lt(a, 3n) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_lt(_, 3n) == True{} : Bool}
  h

# fewer than 3 metrics: no confidence
def ag.none_lt(n: Nat, -b: Maybe<&2, ArD.Dec>, -x: Maybe<&2, ArD.Dec>, -vs: List<&2, ArD.Dec>, h: {Nat.is_lt(n, 3n) == True{} : Bool}) -> {ArT.conf.count(Nat.is_le(3n, n), b, x, vs, n) == None{} : Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              match r:
                case 0n:
                  ag.ft({ArT.conf.count(Nat.is_le(3n, 3n), b, x, vs, 3n) == None{} : Maybe<&2, Nat>}, h)
                case 1n+u:
                  ag.ft({ArT.conf.count(Nat.is_le(3n, 4n+u), b, x, vs, 4n+u) == None{} : Maybe<&2, Nat>}, h)
