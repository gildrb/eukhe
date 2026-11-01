# eukhe: the proof of LAW cron_serve_recover_is_model
# serve is the spec (cron_serve_exact). The spec clears j's id when one of
# the claim records of j's id is cleared (pmr.r1); j's claim records are
# the model's claim of j, whose verdict (the dispatch run here exactly when
# p runs j) is the model's (pmr.cl). The answer at k records the cleared
# flag (LPM.pm.recover_at); applied, it is the model's recovery
# (cron_recover_refines).

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

def pmr.any(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +cs: List<&2, Sv.CRec>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      Bool.or(CronServe.sv_clears(me, runs, dead, c), pmr.any(me, runs, dead, t))

def pmr.k(+b: Bool, +e: Bool, +me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +i: Nat, +d: String, +x: Nat, +o: Nat, +l: List<&2, Nat>, +r: List<&2, Sv.CRec>, +eb: {CronServe.sv_clears(me, runs, dead, Sv.CKnown{d, x, o}) == b : Bool}, +ee: {Nat.is_eq(x, i) == e : Bool}, +ih: {CronServe.sv_has(i, l) == pmr.any(me, runs, dead, r) : Bool}) -> {CronServe.sv_has(i, CronServe.sv_cleared.pick(b, x, l)) == pmr.any(me, runs, dead, CronServeModel.cm_cpick(e, Sv.CKnown{d, x, o}, r)) : Bool}:
  match b e:
    case True{} True{}:
      %Equal.sym(Bool, Nat.is_eq(x, i), True{}, ee) : {Bool.or(_, CronServe.sv_has(i, l)) == Bool.or(CronServe.sv_clears(me, runs, dead, Sv.CKnown{d, x, o}), pmr.any(me, runs, dead, r)) : Bool}
      %Equal.sym(Bool, CronServe.sv_clears(me, runs, dead, Sv.CKnown{d, x, o}), True{}, eb) : {Bool.or(True{}, CronServe.sv_has(i, l)) == Bool.or(_, pmr.any(me, runs, dead, r)) : Bool}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_eq(x, i), False{}, ee) : {Bool.or(_, CronServe.sv_has(i, l)) == pmr.any(me, runs, dead, r) : Bool}
      ih
    case False{} True{}:
      %Equal.sym(Bool, CronServe.sv_clears(me, runs, dead, Sv.CKnown{d, x, o}), False{}, eb) : {CronServe.sv_has(i, l) == Bool.or(_, pmr.any(me, runs, dead, r)) : Bool}
      ih
    case False{} False{}:
      ih

# the spec clears j's id exactly when it clears a claim record of j's id
def pmr.r1(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +i: Nat, +cs: List<&2, Sv.CRec>) -> {CronServe.sv_has(i, CronServe.sv_cleared(me, runs, dead, cs)) == pmr.any(me, runs, dead, CronServeModel.cm_claims_of(i, cs)) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case Sv.CKnown{+d, +x, +o}:
          pmr.k(CronServe.sv_clears(me, runs, dead, Sv.CKnown{d, x, o}), Nat.is_eq(x, i), me, runs, dead, i, d, x, o, CronServe.sv_cleared(me, runs, dead, t), CronServeModel.cm_claims_of(i, t), {==}, {==}, pmr.r1(me, runs, dead, i, t))
        case Sv.CRaw{}:
          pmr.r1(me, runs, dead, i, t)

def pmr.or_f(+a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pmr.own(+own: Bool, +me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +d: String, +o: Nat, +rs: List<&2, Nat>, +run: {CronServe.sv_in(d, runs) == Cr.has(me, rs) : Bool}) -> {CronStore.clear_spec(CronServe.sv_who(own, d, o, runs, dead)) == CronStore.clear_spec(Cron.who_of.pick(own, me, o, rs, dead)) : Bool}:
  match own:
    case True{}:
      %Equal.sym(Bool, CronServe.sv_in(d, runs), Cr.has(me, rs), run) : {CronStore.clear_spec(CS.Mine{_}) == CronStore.clear_spec(CS.Mine{Cr.has(me, rs)}) : Bool}
      {==}
    case False{}:
      %LSx.sx.has(o, dead) : {CronStore.clear_spec(CS.Theirs{_}) == CronStore.clear_spec(CS.Theirs{Cr.has(o, dead)}) : Bool}
      {==}

# the verdict on j's claim record is the model's
def pmr.cl(+j: Cr.Job, +me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +d: String, +run: {CronServe.sv_in(d, runs) == Cr.has(me, Cron.runs_of(j)) : Bool}) -> {pmr.any(me, runs, dead, CronServeModel.cm_claim_rec(j, d)) == Cron.cleared_of(me, dead, j) : Bool}:
  match j:
    case Cr.Job{+i, s, st, nx, kk, cl, +rs, ss, h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{oc, +o}:
              %Equal.sym(Bool, Bool.or(CronStore.clear_spec(CronServe.sv_who(Nat.is_eq(o, me), d, o, runs, dead)), False{}), CronStore.clear_spec(CronServe.sv_who(Nat.is_eq(o, me), d, o, runs, dead)), pmr.or_f(CronStore.clear_spec(CronServe.sv_who(Nat.is_eq(o, me), d, o, runs, dead)))) : {_ == CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(o, me), me, o, rs, dead)) : Bool}
              pmr.own(Nat.is_eq(o, me), me, runs, dead, d, o, rs, run)

def pmr.p2(+cs: List<&2, Sv.CRec>, +runs: List<&2, String>, +p: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +d: String, +rec: {CronServeModel.cm_claims_of(Cr.Job.id(j), cs) == CronServeModel.cm_claim_rec(j, d) : List<&2, Sv.CRec>}, +run: {CronServe.sv_in(d, runs) == Cr.has(p, Cron.runs_of(j)) : Bool}) -> {CronServe.sv_has(Cr.Job.id(j), CronServe.sv_cleared(p, runs, dead, cs)) == Cron.cleared_of(p, dead, j) : Bool}:
  Equal.trans(Bool, CronServe.sv_has(Cr.Job.id(j), CronServe.sv_cleared(p, runs, dead, cs)), pmr.any(p, runs, dead, CronServeModel.cm_claims_of(Cr.Job.id(j), cs)), Cron.cleared_of(p, dead, j), pmr.r1(p, runs, dead, Cr.Job.id(j), cs), Equal.trans(Bool, pmr.any(p, runs, dead, CronServeModel.cm_claims_of(Cr.Job.id(j), cs)), pmr.any(p, runs, dead, CronServeModel.cm_claim_rec(j, d)), Cron.cleared_of(p, dead, j), Equal.cong(List<&2, Sv.CRec>, Bool, l => pmr.any(p, runs, dead, l), CronServeModel.cm_claims_of(Cr.Job.id(j), cs), CronServeModel.cm_claim_rec(j, d), rec), pmr.cl(j, p, runs, dead, d, run)))

def pmr.p3(+j: Cr.Job, +p: Nat, +c: Nat, +dead: List<&2, Nat>, +x: Bool, +hc: {x == Cron.cleared_of(p, dead, j) : Bool}, +alive: {Cr.has(p, dead) == False{} : Bool}) -> {CronServeModel.cm_applied(Sv.JBack{CronStore.recover_spec(Cron.fact_of(j, 60000n), x)}, j, p, Cron.cleared_of(p, dead, j)) == Cron.view(Cr.job(Cr.Recover{p}, c, dead, j), 60000n) : Cron.View()}:
  %Equal.sym(Bool, x, Cron.cleared_of(p, dead, j), hc) : {Cron.back_view(CronStore.recover_spec(Cron.fact_of(j, 60000n), _), Cron.cleared_of(p, dead, j), j, 60000n) == Cron.view(Cr.recover(p, dead, j), 60000n) : Cron.View()}
  Cron.cron_recover_refines(59999n, p, dead, j, alive)

def CronServeModel.cron_serve_recover_is_model(rs, cs, runs, p, c, dead, k, j, d, at, alive, rec, run):
  +hc = pmr.p2(cs, runs, p, dead, j, d, rec, run)
  (Sv.JBack{CronStore.recover_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), CronServe.sv_cleared(p, runs, dead, cs)))}, (Equal.trans(Maybe<&2, Sv.JOut>, CronServeModel.cm_at(Sv.serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.ORecover{dead}), k), CronServeModel.cm_at(CronServe.sv_serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.ORecover{dead}), k), Some{Sv.JBack{CronStore.recover_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), CronServe.sv_cleared(p, runs, dead, cs)))}}, LPM.pm.exact(runs, p, CronServeModel.cm_pj(rs), cs, Sv.ORecover{dead}, k), LPM.pm.recover_at(rs, k, j, CronServe.sv_cleared(p, runs, dead, cs), at)), (hc, pmr.p3(j, p, c, dead, CronServe.sv_has(Cr.Job.id(j), CronServe.sv_cleared(p, runs, dead, cs)), hc, alive))))
