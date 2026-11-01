# eukhe: the proof of LAW cron_serve_finish_unknown
# A dispatch this process does not run changes nothing; one it runs with
# no known claim on record finds none (the premise), and changes nothing
# either. The spec is the stepper's serve (cron_serve_exact).

import Base
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ./base/exact.bend as LSx

def sf.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def sf.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : sf.If(_, G)
  Unit{}

def sf.found(m: Maybe<&2, Sv.Hit>, +me: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, none: {Bool.not(Maybe.is_none(&2, Sv.Hit, m)) == False{} : Bool}) -> {CronServe.sv_finish_found(m, me, False{}, d, ran, failed, now, js, cs) == Sv.Out{False{}, False{}, CronServe.sv_same(js), CronServe.sv_keep(cs)} : Sv.Out}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      sf.absurd({CronServe.sv_finish_found(Some{p}, me, False{}, d, ran, failed, now, js, cs) == Sv.Out{False{}, False{}, CronServe.sv_same(js), CronServe.sv_keep(cs)} : Sv.Out}, none)

def sf.run(b: Bool, +me: Nat, +runs: List<&2, String>, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, none: {Bool.and(b, Bool.not(Maybe.is_none(&2, Sv.Hit, CronServe.sv_claim_of(d, cs)))) == False{} : Bool}) -> {CronServe.sv_reply(CronServe.sv_finish(b, me, runs, False{}, d, ran, failed, now, js, cs)) == Sv.Out{False{}, False{}, CronServe.sv_same(js), CronServe.sv_keep(cs)} : Sv.Out}:
  match b:
    case True{}:
      sf.found(CronServe.sv_claim_of(d, cs), me, d, ran, failed, now, js, cs, none)
    case False{}:
      {==}

def CronServe.cron_serve_finish_unknown(runs, me, js, cs, d, ran, failed, now, none):
  %Equal.sym(Sv.Served, Sv.serve(runs, me, Sv.Parsed{js, cs}, Sv.OFinish{d, ran, failed, now}), CronServe.sv_serve(runs, me, Sv.Parsed{js, cs}, Sv.OFinish{d, ran, failed, now}), LSx.sx.serve(runs, me, Sv.Parsed{js, cs}, Sv.OFinish{d, ran, failed, now})) : {CronServe.sv_reply(_) == Sv.Out{False{}, False{}, CronServe.sv_same(js), CronServe.sv_keep(cs)} : Sv.Out}
  sf.run(CronServe.sv_in(d, runs), me, runs, d, ran, failed, now, js, cs, none)
