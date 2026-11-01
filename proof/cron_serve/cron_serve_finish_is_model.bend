# eukhe: the proof of LAW cron_serve_finish_is_model
# serve is the spec (cron_serve_exact). The spec's finish answers each job
# record kept as read unless this process runs the dispatch and owns its
# first known claim, of job i; then every job of id i counts the result
# (pmf.p1). A job not of id i stays, as in the model. On job i the run and
# the claim are the model's (its), so the spec counts exactly when the
# model's finish counts (cron_finish_refines), and keeps the job as it is
# otherwise, as the model does.

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


# the answer on job j
def pmf.oo(own: Bool, +jh: Nat, +j: Cr.Job, +ran: Bool, +failed: Bool, +now: Nat) -> Sv.JOut:
  match own:
    case True{}:
      CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), jh), Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(j, 60000n), ran, failed, now)})
    case False{}:
      Sv.JSame{}

def pmf.om(m: Maybe<&2, Sv.Hit>, +p: Nat, +j: Cr.Job, +ran: Bool, +failed: Bool, +now: Nat) -> Sv.JOut:
  match m:
    case None{}:
      Sv.JSame{}
    case Some{x}:
      match x:
        case Sv.Hit{jh, +o}:
          pmf.oo(Nat.is_eq(o, p), jh, j, ran, failed, now)

def pmf.o(run: Bool, m: Maybe<&2, Sv.Hit>, +p: Nat, +j: Cr.Job, +ran: Bool, +failed: Bool, +now: Nat) -> Sv.JOut:
  match run:
    case True{}:
      pmf.om(m, p, j, ran, failed, now)
    case False{}:
      Sv.JSame{}

# The answer at k
# ---------------

def pmf.p1o(own: Bool, +rs: List<&2, Cr.Rec>, +k: Nat, +j: Cr.Job, +jh: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +cs: List<&2, Sv.CRec>, at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_jobs(CronServe.sv_finish_own(own, False{}, jh, d, ran, failed, now, CronServeModel.cm_pj(rs), cs)), k) == Some{pmf.oo(own, jh, j, ran, failed, now)} : Maybe<&2, Sv.JOut>}:
  match own:
    case True{}:
      LPM.pm.fj_at(rs, k, j, jh, ran, failed, now, at)
    case False{}:
      LPM.pm.same_at(rs, k, j, at)

def pmf.p1m(m: Maybe<&2, Sv.Hit>, +rs: List<&2, Cr.Rec>, +k: Nat, +p: Nat, +j: Cr.Job, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +cs: List<&2, Sv.CRec>, at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_jobs(CronServe.sv_finish_found(m, p, False{}, d, ran, failed, now, CronServeModel.cm_pj(rs), cs)), k) == Some{pmf.om(m, p, j, ran, failed, now)} : Maybe<&2, Sv.JOut>}:
  match m:
    case None{}:
      LPM.pm.same_at(rs, k, j, at)
    case Some{x}:
      match x:
        case Sv.Hit{+jh, +o}:
          pmf.p1o(Nat.is_eq(o, p), rs, k, j, jh, d, ran, failed, now, cs, at)

def pmf.p1(run: Bool, +rs: List<&2, Cr.Rec>, +k: Nat, +p: Nat, +runs: List<&2, String>, +j: Cr.Job, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +cs: List<&2, Sv.CRec>, at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_jobs(CronServe.sv_reply(CronServe.sv_finish(run, p, runs, False{}, d, ran, failed, now, CronServeModel.cm_pj(rs), cs))), k) == Some{pmf.o(run, CronServe.sv_claim_of(d, cs), p, j, ran, failed, now)} : Maybe<&2, Sv.JOut>}:
  match run:
    case True{}:
      pmf.p1m(CronServe.sv_claim_of(d, cs), rs, k, p, j, d, ran, failed, now, cs, at)
    case False{}:
      LPM.pm.same_at(rs, k, j, at)

# A job not of id i stays
# -----------------------

def pmf.vfo(own: Bool, +jh: Nat, +i: Nat, +j: Cr.Job, +p: Nat, +ran: Bool, +failed: Bool, +now: Nat, hb: {Nat.is_eq(Cr.Job.id(j), i) == False{} : Bool}, hits: {Nat.is_eq(jh, i) == True{} : Bool}) -> {CronServeModel.cm_applied(pmf.oo(own, jh, j, ran, failed, now), j, p, False{}) == Cron.view(j, 60000n) : Cron.View()}:
  match own:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(Cr.Job.id(j), jh), False{}, Equal.trans(Bool, Nat.is_eq(Cr.Job.id(j), jh), Nat.is_eq(Cr.Job.id(j), i), False{}, Equal.cong(Nat, Bool, x => Nat.is_eq(Cr.Job.id(j), x), jh, i, LG.lg.eq_true(jh, i, hits)), hb)) : {CronServeModel.cm_applied(CronServe.sv_if(_, Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(j, 60000n), ran, failed, now)}), j, p, False{}) == Cron.view(j, 60000n) : Cron.View()}
      {==}
    case False{}:
      {==}

def pmf.vf(run: Bool, m: Maybe<&2, Sv.Hit>, +i: Nat, +j: Cr.Job, +p: Nat, +ran: Bool, +failed: Bool, +now: Nat, hb: {Nat.is_eq(Cr.Job.id(j), i) == False{} : Bool}, hits: {CronServeModel.cm_hits(m, i) == True{} : Bool}) -> {CronServeModel.cm_applied(pmf.o(run, m, p, j, ran, failed, now), j, p, False{}) == Cron.view(j, 60000n) : Cron.View()}:
  match run:
    case False{}:
      {==}
    case True{}:
      match m:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Sv.Hit{+jh, +o}:
              pmf.vfo(Nat.is_eq(o, p), jh, i, j, p, ran, failed, now, hb, hits)

# Job i
# -----

def pmf.vto(own: Bool, +ji: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +kk: Nat, +oc: Nat, +o2: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +jh: Nat, +o1: Nat, +i: Nat, +p: Nat, +c: Nat, +out: Cr.Out, eown: {Nat.is_eq(o1, p) == own : Bool}, hb: {Nat.is_eq(ji, i) == True{} : Bool}, hits: {Nat.is_eq(jh, i) == True{} : Bool}, ho: {Nat.is_eq(o1, o2) == True{} : Bool}, hr: {Cr.has(p, rs) == True{} : Bool}) -> {CronServeModel.cm_applied(pmf.oo(own, jh, Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n)), Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, p, False{}) == Cron.view(Cr.finish(p, c, out, Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}), 60000n) : Cron.View()}:
  match own:
    case True{}:
      +e12 = LG.lg.eq_true(o1, o2, ho)
      +e1p = LG.lg.eq_true(o1, p, eown)
      %Equal.sym(Bool, Nat.is_eq(ji, jh), True{}, Equal.trans(Bool, Nat.is_eq(ji, jh), Nat.is_eq(ji, i), True{}, Equal.cong(Nat, Bool, x => Nat.is_eq(ji, x), jh, i, LG.lg.eq_true(jh, i, hits)), hb)) : {CronServeModel.cm_applied(CronServe.sv_if(_, Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, 60000n), Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n))}), Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, p, False{}) == Cron.view(Cr.finish(p, c, out, Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}), 60000n) : Cron.View()}
      Cron.cron_finish_refines(59999n, p, c, out, oc, Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, hr, Equal.cong(Nat, Maybe<&2, Cr.Claim>, x => Some{Cr.Claim{oc, x}}, o2, p, Equal.trans(Nat, o2, o1, p, Equal.sym(Nat, o1, o2, e12), e1p)))
    case False{}:
      %Equal.sym(Bool, Cr.has(p, rs), True{}, hr) : {Cron.view(Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, 60000n) == Cron.view(Cr.finish.run(_, p, c, out, ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h), 60000n) : Cron.View()}
      %Equal.sym(Bool, Nat.is_eq(o2, p), False{}, Equal.trans(Bool, Nat.is_eq(o2, p), Nat.is_eq(o1, p), False{}, Equal.cong(Nat, Bool, x => Nat.is_eq(x, p), o2, o1, Equal.sym(Nat, o1, o2, LG.lg.eq_true(o1, o2, ho))), eown)) : {Cron.view(Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, 60000n) == Cron.view(Cr.finish.own(_, Cr.Claim{oc, o2}, c, out, ji, s, st, nx, kk, Cr.drop(p, rs), ss, h), 60000n) : Cron.View()}
      {==}

def pmf.not_f(+b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  LSf.sg.not_t(b, h)

def pmf.vt(j: Cr.Job, run: Bool, m: Maybe<&2, Sv.Hit>, +i: Nat, +p: Nat, +c: Nat, +out: Cr.Out, hb: {Nat.is_eq(Cr.Job.id(j), i) == True{} : Bool}, hits: {CronServeModel.cm_hits(m, i) == True{} : Bool}, +its: {Bool.and(CronServeModel.cm_beq(run, Cr.has(p, Cron.runs_of(j))), CronServeModel.cm_hit_is(j, m)) == True{} : Bool}) -> {CronServeModel.cm_applied(pmf.o(run, m, p, j, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n)), j, p, False{}) == Cron.view(Cr.finish(p, c, out, j), 60000n) : Cron.View()}:
  match j:
    case Cr.Job{+ji, +s, +st, +nx, +kk, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          match run:
            case False{}:
              %Equal.sym(Bool, Cr.has(p, rs), False{}, pmf.not_f(Cr.has(p, rs), LG.lg.and_l(Bool.not(Cr.has(p, rs)), CronServeModel.cm_hit_is(Cr.Job{ji, s, st, nx, kk, None{}, rs, ss, h}, m), its))) : {Cron.view(Cr.Job{ji, s, st, nx, kk, None{}, rs, ss, h}, 60000n) == Cron.view(Cr.finish.run(_, p, c, out, ji, s, st, nx, kk, None{}, rs, ss, h), 60000n) : Cron.View()}
              {==}
            case True{}:
              match m:
                case None{}:
                  %Equal.sym(Bool, Cr.has(p, rs), True{}, LG.lg.and_l(Cr.has(p, rs), True{}, its)) : {Cron.view(Cr.Job{ji, s, st, nx, kk, None{}, rs, ss, h}, 60000n) == Cron.view(Cr.finish.run(_, p, c, out, ji, s, st, nx, kk, None{}, rs, ss, h), 60000n) : Cron.View()}
                  {==}
                case Some{x}:
                  LG.lg.ft({CronServeModel.cm_applied(pmf.om(Some{x}, p, Cr.Job{ji, s, st, nx, kk, None{}, rs, ss, h}, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n)), Cr.Job{ji, s, st, nx, kk, None{}, rs, ss, h}, p, False{}) == Cron.view(Cr.finish(p, c, out, Cr.Job{ji, s, st, nx, kk, None{}, rs, ss, h}), 60000n) : Cron.View()}, LG.lg.and_r(Cr.has(p, rs), False{}, its))
        case Some{y}:
          match y:
            case Cr.Claim{+oc, +o2}:
              match run:
                case False{}:
                  %Equal.sym(Bool, Cr.has(p, rs), False{}, pmf.not_f(Cr.has(p, rs), LG.lg.and_l(Bool.not(Cr.has(p, rs)), CronServeModel.cm_hit_is(Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, m), its))) : {Cron.view(Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, 60000n) == Cron.view(Cr.finish.run(_, p, c, out, ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h), 60000n) : Cron.View()}
                  {==}
                case True{}:
                  match m:
                    case None{}:
                      LG.lg.ft({CronServeModel.cm_applied(pmf.om(None{}, p, Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n)), Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}, p, False{}) == Cron.view(Cr.finish(p, c, out, Cr.Job{ji, s, st, nx, kk, Some{Cr.Claim{oc, o2}}, rs, ss, h}), 60000n) : Cron.View()}, LG.lg.and_r(Cr.has(p, rs), False{}, its))
                    case Some{x}:
                      match x:
                        case Sv.Hit{+jh, +o1}:
                          pmf.vto(Nat.is_eq(o1, p), ji, s, st, nx, kk, oc, o2, rs, ss, h, jh, o1, i, p, c, out, {==}, hb, hits, LG.lg.and_r(Cr.has(p, rs), Nat.is_eq(o1, o2), its), LG.lg.and_l(Cr.has(p, rs), Nat.is_eq(o1, o2), its))

def pmf.v(b: Bool, run: Bool, m: Maybe<&2, Sv.Hit>, +i: Nat, +j: Cr.Job, +p: Nat, +c: Nat, +out: Cr.Out, hb: {Nat.is_eq(Cr.Job.id(j), i) == b : Bool}, hits: {CronServeModel.cm_hits(m, i) == True{} : Bool}, its: {CronServeModel.cm_its(b, run, Cr.has(p, Cron.runs_of(j)), m, j) == True{} : Bool}) -> {CronServeModel.cm_applied(pmf.o(run, m, p, j, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n)), j, p, False{}) == Cron.view(Cr.job.pick(b, Cr.finish(p, c, out, j), j), 60000n) : Cron.View()}:
  match b:
    case True{}:
      pmf.vt(j, run, m, i, p, c, out, hb, hits, its)
    case False{}:
      pmf.vf(run, m, i, j, p, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n), hb, hits)

def CronServeModel.cron_serve_finish_is_model(rs, cs, runs, p, c, dead, k, j, i, out, d, at, hits, its):
  +op = {Sv.OFinish{d, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n)} : Sv.Op}
  +o = pmf.o(CronServe.sv_in(d, runs), CronServe.sv_claim_of(d, cs), p, j, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n))
  (o, (Equal.trans(Maybe<&2, Sv.JOut>, CronServeModel.cm_at(Sv.serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, op), k), CronServeModel.cm_at(CronServe.sv_serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, op), k), Some{o}, LPM.pm.exact(runs, p, CronServeModel.cm_pj(rs), cs, op, k), pmf.p1(CronServe.sv_in(d, runs), rs, k, p, runs, j, d, Cron.ran_of(out), Cron.failed_of(out), Nat.mul(c, 60000n), cs, at)), pmf.v(Nat.is_eq(Cr.Job.id(j), i), CronServe.sv_in(d, runs), CronServe.sv_claim_of(d, cs), i, j, p, c, out, {==}, hits, its)))
