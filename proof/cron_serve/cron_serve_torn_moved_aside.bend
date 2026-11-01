# eukhe: the proof of LAW cron_serve_torn_moved_aside
# An unreadable file and a missing one both run the update on no records
# (Sv.go with no job and no claim record); they differ only in the aside
# flag, which go copies into the answer. A read file runs go with the flag
# False, and every update's answer carries it (a case split on the update,
# then on the finish's branches).

import Base
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe

# the empty file: the unreadable one answers what the empty one does, but
# moves it aside

def st.fin(b: Bool, +runs: List<&2, String>, +me: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat) -> {Sv.finish(b, me, runs, True{}, d, ran, failed, now, Nil{}, Nil{}) == Sv.Served{CronServe.sv_after(Sv.finish(b, me, runs, False{}, d, ran, failed, now, Nil{}, Nil{})), Sv.Out{True{}, CronServe.sv_write(CronServe.sv_reply(Sv.finish(b, me, runs, False{}, d, ran, failed, now, Nil{}, Nil{}))), CronServe.sv_jobs(CronServe.sv_reply(Sv.finish(b, me, runs, False{}, d, ran, failed, now, Nil{}, Nil{}))), CronServe.sv_claims_out(CronServe.sv_reply(Sv.finish(b, me, runs, False{}, d, ran, failed, now, Nil{}, Nil{})))}} : Sv.Served}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def st.empty(+runs: List<&2, String>, +me: Nat, op: Sv.Op) -> {Sv.go(runs, me, True{}, Nil{}, Nil{}, op) == Sv.Served{CronServe.sv_after(Sv.go(runs, me, False{}, Nil{}, Nil{}, op)), Sv.Out{True{}, CronServe.sv_write(CronServe.sv_reply(Sv.go(runs, me, False{}, Nil{}, Nil{}, op))), CronServe.sv_jobs(CronServe.sv_reply(Sv.go(runs, me, False{}, Nil{}, Nil{}, op))), CronServe.sv_claims_out(CronServe.sv_reply(Sv.go(runs, me, False{}, Nil{}, Nil{}, op)))}} : Sv.Served}:
  match op:
    case Sv.OClaim{due, now, fresh}:
      {==}
    case Sv.ORecover{dead}:
      {==}
    case Sv.OFinish{+d, +ran, +failed, +now}:
      st.fin(Sv.has_str(d, runs), runs, me, d, ran, failed, now)
    case Sv.OCancel{n}:
      {==}
    case Sv.OResume{n, now}:
      {==}
    case Sv.OCreate{n, f}:
      {==}

# a read file is never moved aside

def st.own(own: Bool, +j: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {CronServe.sv_aside(Sv.finish.own(own, False{}, j, d, ran, failed, now, js, cs)) == False{} : Bool}:
  match own:
    case True{}:
      {==}
    case False{}:
      {==}

def st.found(m: Maybe<&2, Sv.Hit>, +me: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {CronServe.sv_aside(Sv.finish.found(m, me, False{}, d, ran, failed, now, js, cs)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Sv.Hit{+j, +o}:
          st.own(Nat.is_eq(o, me), j, d, ran, failed, now, js, cs)

def st.finish(b: Bool, +me: Nat, +runs: List<&2, String>, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {CronServe.sv_aside(CronServe.sv_reply(Sv.finish(b, me, runs, False{}, d, ran, failed, now, js, cs))) == False{} : Bool}:
  match b:
    case True{}:
      st.found(Sv.claim_of(d, cs), me, d, ran, failed, now, js, cs)
    case False{}:
      {==}

def st.claim_end(+runs: List<&2, String>, +cs: List<&2, Sv.CRec>, p: Sv.Pass) -> {CronServe.sv_aside(CronServe.sv_reply(Sv.claim.end(False{}, runs, cs, p))) == False{} : Bool}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def st.read(+runs: List<&2, String>, +me: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, op: Sv.Op) -> {CronServe.sv_aside(CronServe.sv_reply(Sv.go(runs, me, False{}, js, cs, op))) == False{} : Bool}:
  match op:
    case Sv.OClaim{+due, +now, +fresh}:
      st.claim_end(runs, cs, Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now))
    case Sv.ORecover{dead}:
      {==}
    case Sv.OFinish{+d, +ran, +failed, +now}:
      st.finish(Sv.has_str(d, runs), me, runs, d, ran, failed, now, js, cs)
    case Sv.OCancel{n}:
      {==}
    case Sv.OResume{n, now}:
      {==}
    case Sv.OCreate{n, f}:
      {==}

def CronServe.cron_serve_torn_moved_aside(runs, me, js, cs, op):
  (st.empty(runs, me, op), ({==}, st.read(runs, me, js, cs, op)))
