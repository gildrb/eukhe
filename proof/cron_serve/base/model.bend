# eukhe: lemmas the proofs of laws/cron_serve/model.bend share: a model
# file's record at a position, and the answer at a position of the spec's
# per-record maps.

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/cron_serve.bend as Sv
import ../../../laws/cron.bend as Cron
import ../../../laws/cron_store.bend as CronStore
import ../../../laws/cron_serve/serve.bend as CronServe
import ../../../laws/cron_serve/model.bend as CronServeModel
import ./safety.bend as LSf
import ./logic.bend as LG

def pm.job0() -> Cr.Job:
  Cr.Job{0n, Cr.Once{0n}, Cr.Active{}, None{}, 0n, None{}, Nil{}, Nil{}, Nil{}}

def pm.job_of(+r: Cr.Rec) -> Cr.Job:
  match r:
    case Cr.Known{j}:
      j
    case Cr.Raw{x}:
      pm.job0()

def pm.kn(+j0: Cr.Job, +j: Cr.Job, +e: {Some{Cr.Known{j0}} == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {j0 == j : Cr.Job}:
  Equal.cong(Cr.Rec, Cr.Job, r => pm.job_of(r), Cr.Known{j0}, Cr.Known{j}, LSf.sg.some_inj(Cr.Rec, Cr.Known{j0}, Cr.Known{j}, e))

def pm.isk(+r: Cr.Rec, G: Type) -> Type:
  match r:
    case Cr.Known{j}:
      Unit
    case Cr.Raw{x}:
      G

def pm.raw_kn(+x: Nat, +j: Cr.Job, -G: Type, +e: {Some{Cr.Raw{x}} == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> G:
  %Equal.sym(Cr.Rec, Cr.Raw{x}, Cr.Known{j}, LSf.sg.some_inj(Cr.Rec, Cr.Raw{x}, Cr.Known{j}, e)) : pm.isk(_, G)
  Unit{}

# serve on a read file is the spec's
def pm.exact(+runs: List<&2, String>, +me: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, +op: Sv.Op, +k: Nat) -> {CronServeModel.cm_at(Sv.serve(runs, me, Sv.Parsed{js, cs}, op), k) == CronServeModel.cm_at(CronServe.sv_serve(runs, me, Sv.Parsed{js, cs}, op), k) : Maybe<&2, Sv.JOut>}:
  Equal.cong(Sv.Served, Maybe<&2, Sv.JOut>, r => CronServeModel.cm_at(r, k), Sv.serve(runs, me, Sv.Parsed{js, cs}, op), CronServe.sv_serve(runs, me, Sv.Parsed{js, cs}, op), CronServe.cron_serve_exact(runs, me, Sv.Parsed{js, cs}, op))

# the answer at position k of a per-record map
def pm.cancel_at(+rs: List<&2, Cr.Rec>, +k: Nat, +j: Cr.Job, +n: Nat, +at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_cancel_jobs(n, CronServeModel.cm_pj(rs)), k) == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JCut{CronStore.cancel_spec(Cron.fact_of(j, 60000n))})} : Maybe<&2, Sv.JOut>}:
  match rs:
    case Nil{}:
      LSf.sg.none_some(Cr.Rec, Cr.Known{j}, {List.get(&2, Sv.JOut, Nil{}, k) == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JCut{CronStore.cancel_spec(Cron.fact_of(j, 60000n))})} : Maybe<&2, Sv.JOut>}, at)
    case r <> t:
      match r:
        case Cr.Known{+j0}:
          match k:
            case 0n:
              %pm.kn(j0, j, at) : {Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j0), n), Sv.JCut{CronStore.cancel_spec(Cron.fact_of(j0, 60000n))})} == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(_), n), Sv.JCut{CronStore.cancel_spec(Cron.fact_of(_, 60000n))})} : Maybe<&2, Sv.JOut>}
              {==}
            case 1n+q:
              pm.cancel_at(t, q, j, n, at)
        case Cr.Raw{+x}:
          match k:
            case 0n:
              pm.raw_kn(x, j, {Some{Sv.JSame{}} == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JCut{CronStore.cancel_spec(Cron.fact_of(j, 60000n))})} : Maybe<&2, Sv.JOut>}, at)
            case 1n+q:
              pm.cancel_at(t, q, j, n, at)

def pm.resume_at(+rs: List<&2, Cr.Rec>, +k: Nat, +j: Cr.Job, +n: Nat, +now: Nat, +at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_resume_jobs(n, now, CronServeModel.cm_pj(rs)), k) == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JAgain{CronStore.resume_spec(Cron.fact_of(j, 60000n), now)})} : Maybe<&2, Sv.JOut>}:
  match rs:
    case Nil{}:
      LSf.sg.none_some(Cr.Rec, Cr.Known{j}, {List.get(&2, Sv.JOut, Nil{}, k) == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JAgain{CronStore.resume_spec(Cron.fact_of(j, 60000n), now)})} : Maybe<&2, Sv.JOut>}, at)
    case r <> t:
      match r:
        case Cr.Known{+j0}:
          match k:
            case 0n:
              %pm.kn(j0, j, at) : {Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j0), n), Sv.JAgain{CronStore.resume_spec(Cron.fact_of(j0, 60000n), now)})} == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(_), n), Sv.JAgain{CronStore.resume_spec(Cron.fact_of(_, 60000n), now)})} : Maybe<&2, Sv.JOut>}
              {==}
            case 1n+q:
              pm.resume_at(t, q, j, n, now, at)
        case Cr.Raw{+x}:
          match k:
            case 0n:
              pm.raw_kn(x, j, {Some{Sv.JSame{}} == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), n), Sv.JAgain{CronStore.resume_spec(Cron.fact_of(j, 60000n), now)})} : Maybe<&2, Sv.JOut>}, at)
            case 1n+q:
              pm.resume_at(t, q, j, n, now, at)

def pm.recover_at(+rs: List<&2, Cr.Rec>, +k: Nat, +j: Cr.Job, +ids: List<&2, Nat>, +at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_recover_jobs(ids, CronServeModel.cm_pj(rs)), k) == Some{Sv.JBack{CronStore.recover_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), ids))}} : Maybe<&2, Sv.JOut>}:
  match rs:
    case Nil{}:
      LSf.sg.none_some(Cr.Rec, Cr.Known{j}, {List.get(&2, Sv.JOut, Nil{}, k) == Some{Sv.JBack{CronStore.recover_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), ids))}} : Maybe<&2, Sv.JOut>}, at)
    case r <> t:
      match r:
        case Cr.Known{+j0}:
          match k:
            case 0n:
              %pm.kn(j0, j, at) : {Some{Sv.JBack{CronStore.recover_spec(Cron.fact_of(j0, 60000n), CronServe.sv_has(Cr.Job.id(j0), ids))}} == Some{Sv.JBack{CronStore.recover_spec(Cron.fact_of(_, 60000n), CronServe.sv_has(Cr.Job.id(_), ids))}} : Maybe<&2, Sv.JOut>}
              {==}
            case 1n+q:
              pm.recover_at(t, q, j, ids, at)
        case Cr.Raw{+x}:
          match k:
            case 0n:
              pm.raw_kn(x, j, {Some{Sv.JSame{}} == Some{Sv.JBack{CronStore.recover_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), ids))}} : Maybe<&2, Sv.JOut>}, at)
            case 1n+q:
              pm.recover_at(t, q, j, ids, at)

def pm.same_at(+rs: List<&2, Cr.Rec>, +k: Nat, +j: Cr.Job, +at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_same(CronServeModel.cm_pj(rs)), k) == Some{Sv.JSame{}} : Maybe<&2, Sv.JOut>}:
  match rs:
    case Nil{}:
      LSf.sg.none_some(Cr.Rec, Cr.Known{j}, {List.get(&2, Sv.JOut, Nil{}, k) == Some{Sv.JSame{}} : Maybe<&2, Sv.JOut>}, at)
    case r <> t:
      match r:
        case Cr.Known{j0}:
          match k:
            case 0n:
              {==}
            case 1n+q:
              pm.same_at(t, q, j, at)
        case Cr.Raw{x}:
          match k:
            case 0n:
              {==}
            case 1n+q:
              pm.same_at(t, q, j, at)

def pm.fj_at(+rs: List<&2, Cr.Rec>, +k: Nat, +j: Cr.Job, +jh: Nat, +ran: Bool, +failed: Bool, +now: Nat, +at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}) -> {List.get(&2, Sv.JOut, CronServe.sv_finish_jobs(jh, ran, failed, now, CronServeModel.cm_pj(rs)), k) == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), jh), Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(j, 60000n), ran, failed, now)})} : Maybe<&2, Sv.JOut>}:
  match rs:
    case Nil{}:
      LSf.sg.none_some(Cr.Rec, Cr.Known{j}, {List.get(&2, Sv.JOut, Nil{}, k) == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), jh), Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(j, 60000n), ran, failed, now)})} : Maybe<&2, Sv.JOut>}, at)
    case r <> t:
      match r:
        case Cr.Known{+j0}:
          match k:
            case 0n:
              %pm.kn(j0, j, at) : {Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j0), jh), Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(j0, 60000n), ran, failed, now)})} == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(_), jh), Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(_, 60000n), ran, failed, now)})} : Maybe<&2, Sv.JOut>}
              {==}
            case 1n+q:
              pm.fj_at(t, q, j, jh, ran, failed, now, at)
        case Cr.Raw{+x}:
          match k:
            case 0n:
              pm.raw_kn(x, j, {Some{Sv.JSame{}} == Some{CronServe.sv_if(Nat.is_eq(Cr.Job.id(j), jh), Sv.JFin{CronStore.finish_spec(60000n, Cron.fact_of(j, 60000n), ran, failed, now)})} : Maybe<&2, Sv.JOut>}, at)
            case 1n+q:
              pm.fj_at(t, q, j, jh, ran, failed, now, at)
