# eukhe: lemmas for the converse log laws of area autoresearch
# (keep_accepted, log_accepted): a log the code accepts is ar_accepts

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../../../spec/autoresearch/segment.bend as SG
import ../../../spec/autoresearch/metric_line.bend as SL
import ../../../laws/autoresearch/model.bend as Autoresearch
import ./log.bend as AgLog

# Contradictions
# --------------

def aa.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True: anything follows
def aa.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : aa.If(_, G)
  Unit{}

def aa.MIf(m: Maybe<&2, Bool>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# no run is not a finished one: anything follows
def aa.none_some(-G: Type, -b: Bool, e: {None{} == Some{b} : Maybe<&2, Bool>}) -> G:
  %e : aa.MIf(_, G)
  Unit{}

def aa.get(m: Maybe<&2, Bool>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      x

# a failed run is not a passed one: anything follows
def aa.failed(-G: Type, e: {Some{False{}} == Some{True{}} : Maybe<&2, Bool>}) -> G:
  aa.absurd(G, Equal.cong(Maybe<&2, Bool>, Bool, m => aa.get(m), Some{False{}}, Some{True{}}, e))

# Accepted logs
# -------------

# log.done is accepted with its effect, its row appended
def aa.done(+cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String, -eff: ArS.Eff) -> Autoresearch.ar_accepts(ArS.St{cfg, seg, mode, runs, Some{p}}, st, desc, ArP.log.done(cfg, seg, mode, runs, p, st, desc, eff), eff):
  ({==}, AgLog.ag.row_snoc(runs, cfg, seg, p, Some{st}, desc), {==}, {==}, {==})

# a log that needs ok, given ok
def aa.need(ok: Bool, e: {ok == True{} : Bool}, -text: String, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +st: ArS.Status, +desc: String) -> Autoresearch.ar_accepts(ArS.St{cfg, seg, mode, runs, Some{p}}, st, desc, ArP.log.need(ok, text, cfg, seg, mode, runs, p, st, desc), ArS.Reset{}):
  match ok:
    case True{}:
      aa.done(cfg, seg, mode, runs, p, st, desc, ArS.Reset{})
    case False{}:
      aa.absurd(Empty, e)

# a keep with its justification
def aa.why(ok: Bool, e: {ok == True{} : Bool}, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String) -> Autoresearch.ar_accepts(ArS.St{cfg, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, ArP.keep.why(ok, cfg, seg, mode, runs, p, desc), ArS.Commit{}):
  match ok:
    case True{}:
      aa.done(cfg, seg, mode, runs, p, ArS.Keep{}, desc, ArS.Commit{})
    case False{}:
      aa.absurd(Empty, e)

# a keep that beats the segment, with its justification
def aa.beats(ok: Bool, e: {ok == True{} : Bool}, +m: ArD.Dec, +dir: ArS.Dir, +why: Maybe<&2, String>, +devs: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, j: {Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}) -> Autoresearch.ar_accepts(ArS.St{cfg, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, ArP.keep.beats(ok, m, dir, why, devs, cfg, seg, mode, runs, p, desc), ArS.Commit{}):
  match ok:
    case True{}:
      aa.why(Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), j, cfg, seg, mode, runs, p, desc)
    case False{}:
      aa.absurd(Empty, e)

# a keep whose metric beats every kept run of the segment (not flagged)
def aa.metric(m: Maybe<&2, ArD.Dec>, +c: ArS.Cfg, +why: Maybe<&2, String>, +devs: Nat, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +p: ArS.Pend, +desc: String, b: Autoresearch.ar_keep_beats.m(m, ArS.Cfg.dir(c), runs, seg), j: {Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}) -> Autoresearch.ar_accepts(ArS.St{Some{c}, seg, mode, runs, Some{p}}, ArS.Keep{}, desc, ArP.keep.metric(m, c, why, devs, seg, mode, runs, p, desc), ArS.Commit{}):
  match m:
    case None{}:
      match b:
    case Some{+x}:
      +dir = ArS.Cfg.dir(c)
      aa.beats(ArS.beats(dir, x, runs, seg), Equal.trans(Bool, ArS.beats(dir, x, runs, seg), SG.all_beaten(~ArD.Dec.cmp, dir, x, runs, seg), True{}, AgLog.ag.beats_eq(dir, x, runs, seg), b), x, dir, why, devs, Some{c}, seg, mode, runs, p, desc, j)

# the law's justification is the code's
def aa.just(+devs: Nat, why: Maybe<&2, String>, j: {Bool.or(Nat.is_eq(devs, 0n), Autoresearch.ar_justified(why)) == True{} : Bool}) -> {Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == True{} : Bool}:
  match why:
    case None{}:
      j
    case Some{+t}:
      %Equal.sym(Bool, ArL.some(t), SL.nonempty(t), AgLog.ag.some_eq(t)) : {Bool.or(Nat.is_eq(devs, 0n), _) == True{} : Bool}
      j
