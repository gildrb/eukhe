# eukhe: the proof of LAW cron_serve_claim_is_model
# serve is the spec (cron_serve_exact). The spec's pass walks the records;
# at each known one its set is the jobs of the claims on record and the
# ids it claimed before, none of which is a later record's id (the ids are
# distinct), so the job at k reads its own claim on record; a fresh id is
# left for every record not yet passed. So the answer at k is the take of
# its facts with its claim on record (pmk.pass); applied, that is the
# model's claim step (cron_take_refines).

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

# none of the ids of rs is in a
def pmk.none(+rs: List<&2, Cr.Rec>, +a: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Cr.Known{j}:
          Bool.and(Bool.not(CronServe.sv_has(Cr.Job.id(j), a)), pmk.none(t, a))
        case Cr.Raw{x}:
          pmk.none(t, a)

def pmk.jo(+p: Sv.Pass) -> List<&2, Sv.JOut>:
  match p:
    case Sv.Pass{jo, cn, ds}:
      jo

def pmk.end(+a: Bool, +runs: List<&2, String>, +cs: List<&2, Sv.CRec>, +p: Sv.Pass) -> {CronServe.sv_jobs(CronServe.sv_reply(CronServe.sv_claim_end(a, runs, cs, p))) == pmk.jo(p) : List<&2, Sv.JOut>}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def pmk.put(+o: Sv.JOut, +p: Sv.Pass) -> {pmk.jo(CronServe.sv_pass_put(o, p)) == o <> pmk.jo(p) : List<&2, Sv.JOut>}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def pmk.add(+b: Bool, +k: Nat, +fresh: List<&2, String>, +o: Sv.JOut, +p: Sv.Pass) -> {pmk.jo(CronServe.sv_pass_add(b, k, fresh, o, p)) == o <> pmk.jo(p) : List<&2, Sv.JOut>}:
  match b:
    case True{}:
      match fresh:
        case Nil{}:
          pmk.put(o, p)
        case d <> r:
          match p:
            case Sv.Pass{jo, cn, ds}:
              {==}
    case False{}:
      pmk.put(o, p)

def pmk.took(+t: CS.Took, +d: String, +r: List<&2, String>) -> {CronServe.sv_took(t, d <> r) == Sv.JTook{t} : Sv.JOut}:
  match t:
    case CS.Keep{}:
      {==}
    case CS.Roll{n}:
      {==}
    case CS.Claimed{n}:
      {==}

def pmk.ta(+b: Bool, +i: Nat, +a: List<&2, Nat>, +t0: List<&2, Nat>) -> {List.append(&2, Nat, CronServe.sv_taken_after(b, i, a), t0) == CronServe.sv_taken_after(b, i, List.append(&2, Nat, a, t0)) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pmk.has_na(+i: Nat, +a: List<&2, Nat>, +t0: List<&2, Nat>, +h: {CronServe.sv_has(i, a) == False{} : Bool}) -> {CronServe.sv_has(i, t0) == CronServe.sv_has(i, List.append(&2, Nat, a, t0)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> r:
      +h2 = h
      %Equal.sym(Bool, Nat.is_eq(x, i), False{}, LSf.sg.or_fl(Nat.is_eq(x, i), CronServe.sv_has(i, r), h)) : {CronServe.sv_has(i, t0) == Bool.or(_, CronServe.sv_has(i, List.append(&2, Nat, r, t0))) : Bool}
      pmk.has_na(i, r, t0, LSf.sg.or_fr(Nat.is_eq(x, i), CronServe.sv_has(i, r), h2))

def pmk.nc(+t: List<&2, Cr.Rec>, +i0: Nat, +a: List<&2, Nat>, +h: {pmk.none(t, a) == True{} : Bool}, +ni: {CronServeModel.cm_has_id(i0, t) == False{} : Bool}) -> {pmk.none(t, i0 <> a) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case r <> u:
      match r:
        case Cr.Known{+j1}:
          +i1 = Cr.Job.id(j1)
          +h2 = h
          +ni2 = ni
          +e1 = Equal.trans(Bool, Nat.is_eq(i0, i1), Nat.is_eq(i1, i0), False{}, LSf.sg.eq_sym(i0, i1), LSf.sg.or_fl(Nat.is_eq(i1, i0), CronServeModel.cm_has_id(i0, u), ni))
          +e2 = LSf.sg.not_t(CronServe.sv_has(i1, a), LG.lg.and_l(Bool.not(CronServe.sv_has(i1, a)), pmk.none(u, a), h))
          %Equal.sym(Bool, Nat.is_eq(i0, i1), False{}, e1) : {Bool.and(Bool.not(Bool.or(_, CronServe.sv_has(i1, a))), pmk.none(u, i0 <> a)) == True{} : Bool}
          %Equal.sym(Bool, CronServe.sv_has(i1, a), False{}, e2) : {Bool.and(Bool.not(Bool.or(False{}, _)), pmk.none(u, i0 <> a)) == True{} : Bool}
          pmk.nc(u, i0, a, LG.lg.and_r(Bool.not(CronServe.sv_has(i1, a)), pmk.none(u, a), h2), LSf.sg.or_fr(Nat.is_eq(i1, i0), CronServeModel.cm_has_id(i0, u), ni2))
        case Cr.Raw{x}:
          pmk.nc(u, i0, a, h, ni)

def pmk.na2(+b: Bool, +t: List<&2, Cr.Rec>, +i0: Nat, +a: List<&2, Nat>, +h: {pmk.none(t, a) == True{} : Bool}, +ni: {CronServeModel.cm_has_id(i0, t) == False{} : Bool}) -> {pmk.none(t, CronServe.sv_taken_after(b, i0, a)) == True{} : Bool}:
  match b:
    case True{}:
      pmk.nc(t, i0, a, h, ni)
    case False{}:
      h

def pmk.none_nil(+rs: List<&2, Cr.Rec>) -> {pmk.none(rs, Nil{}) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case Cr.Known{j}:
          pmk.none_nil(t)
        case Cr.Raw{x}:
          pmk.none_nil(t)

def pmk.le_w(+a: Nat, +b: Nat, +h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LG.lg.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pmk.le_w(p, q, h)

def pmk.en(+b: Bool, +fresh: List<&2, String>, +lt: Nat, +h: {Nat.is_le(1n+lt, List.length(&2, String, fresh)) == True{} : Bool}) -> {Nat.is_le(lt, List.length(&2, String, CronServe.sv_fresh_after(b, fresh))) == True{} : Bool}:
  match b:
    case True{}:
      match fresh:
        case Nil{}:
          LG.lg.ft({Nat.is_le(lt, 0n) == True{} : Bool}, h)
        case d <> r:
          h
    case False{}:
      pmk.le_w(lt, List.length(&2, String, fresh), h)

# the answer at q of the pass over the records rs, from a set of the ids
# claimed before (a, none of rs's) and the jobs of the claims on record
# (t0), with a fresh id for every record left
def pmk.pass(+rs: List<&2, Cr.Rec>, +q: Nat, +k0: Nat, +a: List<&2, Nat>, +t0: List<&2, Nat>, +due: Nat, +now: Nat, +j: Cr.Job, +fresh: List<&2, String>, +at: {List.get(&2, Cr.Rec, rs, q) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}, +ids: {CronServeModel.cm_distinct(rs) == True{} : Bool}, +na: {pmk.none(rs, a) == True{} : Bool}, +enough: {Nat.is_le(List.length(&2, Cr.Rec, rs), List.length(&2, String, fresh)) == True{} : Bool}) -> {List.get(&2, Sv.JOut, pmk.jo(CronServe.sv_pass(CronServeModel.cm_pj(rs), k0, List.append(&2, Nat, a, t0), fresh, due, now)), q) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}:
  match rs:
    case Nil{}:
      LSf.sg.none_some(Cr.Rec, Cr.Known{j}, {List.get(&2, Sv.JOut, pmk.jo(CronServe.sv_pass(Nil{}, k0, List.append(&2, Nat, a, t0), fresh, due, now)), q) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}, at)
    case r <> +t:
      match r:
        case Cr.Known{+j0}:
          match q:
            case 0n:
              match fresh:
                case Nil{}:
                  LG.lg.ft({List.get(&2, Sv.JOut, pmk.jo(CronServe.sv_pass(CronServeModel.cm_pj(Cr.Known{j0} <> t), k0, List.append(&2, Nat, a, t0), Nil{}, due, now)), 0n) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}, enough)
                case +d <> +fr:
                +i0 = Cr.Job.id(j0)
                +f0 = Cron.fact_of(j0, 60000n)
                +tk = CronStore.take_spec(f0, CronServe.sv_has(i0, List.append(&2, Nat, a, t0)), due, now)
                +b = CronServe.sv_claims(tk, d <> fr)
                +rest = CronServe.sv_pass(CronServeModel.cm_pj(t), 1n+k0, CronServe.sv_taken_after(b, i0, List.append(&2, Nat, a, t0)), CronServe.sv_fresh_after(b, d <> fr), due, now)
                %Equal.sym(List<&2, Sv.JOut>, pmk.jo(CronServe.sv_pass_add(b, k0, d <> fr, CronServe.sv_took(tk, d <> fr), rest)), CronServe.sv_took(tk, d <> fr) <> pmk.jo(rest), pmk.add(b, k0, d <> fr, CronServe.sv_took(tk, d <> fr), rest)) : {List.get(&2, Sv.JOut, _, 0n) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}
                  +hn = LSf.sg.not_t(CronServe.sv_has(i0, a), LG.lg.and_l(Bool.not(CronServe.sv_has(i0, a)), pmk.none(t, a), na))
                  %Equal.sym(Sv.JOut, CronServe.sv_took(tk, d <> fr), Sv.JTook{tk}, pmk.took(tk, d, fr)) : {Some{_} == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}
                  %pmk.has_na(i0, a, t0, hn) : {Some{Sv.JTook{CronStore.take_spec(f0, _, due, now)}} == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}
                  %LPM.pm.kn(j0, j, at) : {Some{Sv.JTook{CronStore.take_spec(f0, CronServe.sv_has(i0, t0), due, now)}} == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(_, 60000n), CronServe.sv_has(Cr.Job.id(_), t0), due, now)}} : Maybe<&2, Sv.JOut>}
                  {==}
            case 1n+q2:
              +i0 = Cr.Job.id(j0)
              +f0 = Cron.fact_of(j0, 60000n)
              +tk = CronStore.take_spec(f0, CronServe.sv_has(i0, List.append(&2, Nat, a, t0)), due, now)
              +b = CronServe.sv_claims(tk, fresh)
              +rest = CronServe.sv_pass(CronServeModel.cm_pj(t), 1n+k0, CronServe.sv_taken_after(b, i0, List.append(&2, Nat, a, t0)), CronServe.sv_fresh_after(b, fresh), due, now)
              %Equal.sym(List<&2, Sv.JOut>, pmk.jo(CronServe.sv_pass_add(b, k0, fresh, CronServe.sv_took(tk, fresh), rest)), CronServe.sv_took(tk, fresh) <> pmk.jo(rest), pmk.add(b, k0, fresh, CronServe.sv_took(tk, fresh), rest)) : {List.get(&2, Sv.JOut, _, 1n+q2) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}
              +ids2 = ids
              +na2 = na
              %pmk.ta(b, i0, a, t0) : {List.get(&2, Sv.JOut, pmk.jo(CronServe.sv_pass(CronServeModel.cm_pj(t), 1n+k0, _, CronServe.sv_fresh_after(b, fresh), due, now)), q2) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}
              pmk.pass(t, q2, 1n+k0, CronServe.sv_taken_after(b, i0, a), t0, due, now, j, CronServe.sv_fresh_after(b, fresh), at, LG.lg.and_r(Bool.not(CronServeModel.cm_has_id(i0, t)), CronServeModel.cm_distinct(t), ids), pmk.na2(b, t, i0, a, LG.lg.and_r(Bool.not(CronServe.sv_has(i0, a)), pmk.none(t, a), na), LSf.sg.not_t(CronServeModel.cm_has_id(i0, t), LG.lg.and_l(Bool.not(CronServeModel.cm_has_id(i0, t)), CronServeModel.cm_distinct(t), ids2))), pmk.en(b, fresh, List.length(&2, Cr.Rec, t), enough))
        case Cr.Raw{+x}:
          match q:
            case 0n:
              LPM.pm.raw_kn(x, j, {List.get(&2, Sv.JOut, pmk.jo(CronServe.sv_pass(CronServeModel.cm_pj(Cr.Raw{x} <> t), k0, List.append(&2, Nat, a, t0), fresh, due, now)), 0n) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}, at)
            case 1n+q2:
              +rest = CronServe.sv_pass(CronServeModel.cm_pj(t), 1n+k0, List.append(&2, Nat, a, t0), fresh, due, now)
              %Equal.sym(List<&2, Sv.JOut>, pmk.jo(CronServe.sv_pass_put(Sv.JSame{}, rest)), Sv.JSame{} <> pmk.jo(rest), pmk.put(Sv.JSame{}, rest)) : {List.get(&2, Sv.JOut, _, 1n+q2) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), CronServe.sv_has(Cr.Job.id(j), t0), due, now)}} : Maybe<&2, Sv.JOut>}
              pmk.pass(t, q2, 1n+k0, a, t0, due, now, j, fresh, at, ids, na, pmk.le_w(List.length(&2, Cr.Rec, t), List.length(&2, String, fresh), enough))

# The law
# -------

def pmk.p1(+rs: List<&2, Cr.Rec>, +cs: List<&2, Sv.CRec>, +runs: List<&2, String>, +p: Nat, +c: Nat, +fresh: List<&2, String>, +k: Nat, +j: Cr.Job, +at: {List.get(&2, Cr.Rec, rs, k) == Some{Cr.Known{j}} : Maybe<&2, Cr.Rec>}, +ids: {CronServeModel.cm_distinct(rs) == True{} : Bool}, +cl: {CronServe.sv_has(Cr.Job.id(j), CronServe.sv_taken(cs)) == Cron.claimed_of(j) : Bool}, +enough: {Nat.is_le(List.length(&2, Cr.Rec, rs), List.length(&2, String, fresh)) == True{} : Bool}) -> {CronServeModel.cm_at(CronServe.sv_serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OClaim{Nat.mul(c, 60000n), Nat.mul(c, 60000n), fresh}), k) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), Cron.claimed_of(j), Nat.mul(c, 60000n), Nat.mul(c, 60000n))}} : Maybe<&2, Sv.JOut>}:
  +n = Nat.mul(c, 60000n)
  +pp = CronServe.sv_pass(CronServeModel.cm_pj(rs), 0n, CronServe.sv_taken(cs), fresh, n, n)
  %Equal.sym(List<&2, Sv.JOut>, CronServe.sv_jobs(CronServe.sv_reply(CronServe.sv_claim_end(False{}, runs, cs, pp))), pmk.jo(pp), pmk.end(False{}, runs, cs, pp)) : {List.get(&2, Sv.JOut, _, k) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), Cron.claimed_of(j), n, n)}} : Maybe<&2, Sv.JOut>}
  %cl : {List.get(&2, Sv.JOut, pmk.jo(pp), k) == Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), _, n, n)}} : Maybe<&2, Sv.JOut>}
  pmk.pass(rs, k, 0n, Nil{}, CronServe.sv_taken(cs), n, n, j, fresh, at, ids, pmk.none_nil(rs), enough)

def CronServeModel.cron_serve_claim_is_model(rs, cs, runs, p, c, dead, fresh, k, j, at, ids, cl, enough):
  (Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), Cron.claimed_of(j), Nat.mul(c, 60000n), Nat.mul(c, 60000n))}, (Equal.trans(Maybe<&2, Sv.JOut>, CronServeModel.cm_at(Sv.serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OClaim{Nat.mul(c, 60000n), Nat.mul(c, 60000n), fresh}), k), CronServeModel.cm_at(CronServe.sv_serve(runs, p, Sv.Parsed{CronServeModel.cm_pj(rs), cs}, Sv.OClaim{Nat.mul(c, 60000n), Nat.mul(c, 60000n), fresh}), k), Some{Sv.JTook{CronStore.take_spec(Cron.fact_of(j, 60000n), Cron.claimed_of(j), Nat.mul(c, 60000n), Nat.mul(c, 60000n))}}, LPM.pm.exact(runs, p, CronServeModel.cm_pj(rs), cs, Sv.OClaim{Nat.mul(c, 60000n), Nat.mul(c, 60000n), fresh}, k), pmk.p1(rs, cs, runs, p, c, fresh, k, j, at, ids, cl, enough)), Cron.cron_take_refines(59999n, p, c, j)))
