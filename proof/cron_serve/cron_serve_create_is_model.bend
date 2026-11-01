# eukhe: the proof of LAW cron_serve_create_is_model
# serve is the spec (cron_serve_exact): every record kept as read, the new
# job last, every claim kept; the new job moves the file, so it is
# written. The model's create of a live process appends its new job.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_serve/serve.bend as CronServe
import ../../laws/cron_serve/model.bend as CronServeModel
import ./base/model.bend as LPM
import ./base/safety.bend as LSf
import ./base/logic.bend as LG
import ./base/exact.bend as LSx

def pcr.jm(+js: List<&2, Sv.JRec>) -> {CronServe.sv_jmoves(List.append(&2, Sv.JOut, CronServe.sv_same(js), [Sv.JNew{}])) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> t:
      pcr.jm(t)

def pcr.p1(+rs: List<&2, Cr.Rec>, +cs: List<&2, Sv.CRec>, +runs: List<&2, String>, +p: Nat, +n: Nat, +f: CS.Fact) -> {CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OCreate{n, f})) == Sv.Out{False{}, True{}, List.append(&2, Sv.JOut, CronServe.sv_same(CronServeModel.cm_pj(rs)), [Sv.JNew{}]), CronServe.sv_keep(cs)} : Sv.Out}:
  %Equal.sym(Sv.Served, Sv.serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OCreate{n, f}), CronServe.sv_serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OCreate{n, f}), CronServe.cron_serve_exact(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OCreate{n, f})) : {CronServe.sv_reply(_) == Sv.Out{False{}, True{}, List.append(&2, Sv.JOut, CronServe.sv_same(CronServeModel.cm_pj(rs)), [Sv.JNew{}]), CronServe.sv_keep(cs)} : Sv.Out}
  %Equal.sym(Bool, CronServe.sv_jmoves(List.append(&2, Sv.JOut, CronServe.sv_same(CronServeModel.cm_pj(rs)), [Sv.JNew{}])), True{}, pcr.jm(CronServeModel.cm_pj(rs))) : {Sv.Out{False{}, Bool.or(_, CronServe.sv_cmoves(CronServe.sv_keep(cs))), List.append(&2, Sv.JOut, CronServe.sv_same(CronServeModel.cm_pj(rs)), [Sv.JNew{}]), CronServe.sv_keep(cs)} == Sv.Out{False{}, True{}, List.append(&2, Sv.JOut, CronServe.sv_same(CronServeModel.cm_pj(rs)), [Sv.JNew{}]), CronServe.sv_keep(cs)} : Sv.Out}
  {==}

def pcr.p2(+rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +dead: List<&2, Nat>, +c: Nat, +n: Nat, +aside: List<&2, Nat>, +p: Nat, +sc: Cr.Sched, +alive: {Cr.has(p, dead) == False{} : Bool}) -> {Cr.S.recs(Cr.step(Cr.S{None{}, rs, rd, dead, c, n, aside}, Cr.Create{p, sc})) == List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]) : List<&2, Cr.Rec>}:
  %Equal.sym(Bool, Cr.has(p, dead), False{}, alive) : {Cr.S.recs(Cr.step.alive(_, Cr.S{None{}, List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]), rd, dead, c, 1n+n, Cr.heal(None{}, aside)}, Cr.S{None{}, rs, rd, dead, c, n, aside})) == List.append(&2, Cr.Rec, rs, [Cr.Known{Cr.Job{n, sc, Cr.Active{}, Some{Cr.first(sc, c)}, 0n, None{}, Nil{}, Nil{}, Nil{}}}]) : List<&2, Cr.Rec>}
  {==}

def CronServeModel.cron_serve_create_is_model(rs, cs, runs, p, f, rd, dead, c, n, aside, sc, alive):
  (pcr.p1(rs, cs, runs, p, n, f), pcr.p2(rs, rd, dead, c, n, aside, p, sc, alive))
