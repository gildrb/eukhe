# eukhe: the proof of LAW init_accepted: the configuration has no error
# (AE.ev.err_none); the harness is there when it is needed, and the kind
# is kept on the same segment (AE.ev.same), so the init sets the state,
# whose rows are the old ones and the abandoned pending run
# (AE.ev.abandons)

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/events.bend as AE

def iac.or_false(h: Bool, e: {Bool.or(h, False{}) == True{} : Bool}) -> {h == True{} : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      e

def iac.set(+c: ArS.Cfg, +seg2: Nat, +m: String, -old: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> AutoresearchEvents.ar_init_ok(ArS.St{old, seg, mode, runs, pend}, c, ArP.init.set(c, seg2, m, seg, runs, pend)):
  ({==}, ({==}, AE.ev.abandons(old, seg, mode, runs, pend, m)))

def iac.need(harness: Bool, hs: {harness == True{} : Bool}, +c: ArS.Cfg, +seg2: Nat, +m: String, -old: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> AutoresearchEvents.ar_init_ok(ArS.St{old, seg, mode, runs, pend}, c, ArP.init.need(harness, c, seg2, m, seg, runs, pend)):
  match harness:
    case True{}:
      iac.set(c, seg2, m, old, seg, mode, runs, pend)
    case False{}:
      AS.as.absurd(AutoresearchEvents.ar_init_ok(ArS.St{old, seg, mode, runs, pend}, c, ArP.init.need(False{}, c, seg2, m, seg, runs, pend)), hs)

def iac.old(old: Maybe<&2, ArS.Cfg>, +c: ArS.Cfg, fresh: Bool, +harness: Bool, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hs: {Bool.or(harness, Bool.not(Bool.or(ArM.ar_no_cfg(ArS.St{old, seg, mode, runs, pend}), fresh))) == True{} : Bool}, kind: {AutoresearchEvents.ar_kind_ok(ArS.St{old, seg, mode, runs, pend}, fresh, c) == True{} : Bool}) -> AutoresearchEvents.ar_init_ok(ArS.St{old, seg, mode, runs, pend}, c, ArP.init.old(old, c, fresh, harness, seg, runs, pend)):
  match old:
    case None{}:
      iac.need(harness, iac.or_false(harness, hs), c, seg, "", None{}, seg, mode, runs, pend)
    case Some{+o}:
      match fresh:
        case True{}:
          iac.need(harness, iac.or_false(harness, hs), c, 1n+seg, ArS.Cfg.metric(o), Some{o}, seg, mode, runs, pend)
        case False{}:
          +e = Equal.trans(Bool, ArP.same(o, c), Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), ArM.ar_dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c))), True{}, AE.ev.same(o, c), kind)
          %Equal.sym(Bool, ArP.same(o, c), True{}, e) : AutoresearchEvents.ar_init_ok(ArS.St{Some{o}, seg, mode, runs, pend}, c, ArP.init.keep(_, c, ArS.Cfg.metric(o), seg, runs, pend))
          iac.set(c, seg, ArS.Cfg.metric(o), Some{o}, seg, mode, runs, pend)

def AutoresearchEvents.init_accepted(s, c, fresh, harness, name, cap, hs, kind):
  match s:
    case ArS.St{old, seg, mode, runs, pend}:
      %Equal.sym(Maybe<&2, String>, ArP.init.err(c), None{}, AE.ev.err_none(c, name, cap)) : AutoresearchEvents.ar_init_ok(ArS.St{old, seg, mode, runs, pend}, c, ArP.init.check(_, old, c, fresh, harness, seg, runs, pend))
      iac.old(old, c, fresh, harness, seg, mode, runs, pend, hs, kind)
