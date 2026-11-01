# eukhe: the proof of LAW cron_serve_records_in_place
# Every walk of the serve the stepper runs (bend/cron_serve.bend) answers
# each record in turn, a record this build cannot read with kept-as-read
# (each walk by induction on the records); the claim pass's answers are
# taken apart (rp.pj, rp.pn) to walk them; the claim records' answers are
# kept, then only new claims follow; only a create adds a job, last.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe

def rp.pj(p: Sv.Pass) -> List<&2, Sv.JOut>:
  match p:
    case Sv.Pass{jo, cn, ds}:
      jo

def rp.pn(p: Sv.Pass) -> List<&2, Sv.COut>:
  match p:
    case Sv.Pass{jo, cn, ds}:
      cn

def rp.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# The job answers
# ---------------

def rp.known_same(r: Sv.JRec) -> {CronServe.sv_jplace(r, Sv.JSame{}) == True{} : Bool}:
  match r:
    case Sv.JRaw{}:
      {==}
    case Sv.JKnown{i, f}:
      {==}

def rp.same(js: List<&2, Sv.JRec>) -> {CronServe.sv_jobs_placed(js, Sv.same(js), False{}) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case +r <> +t:
      rp.and_t(CronServe.sv_jplace(r, Sv.JSame{}), CronServe.sv_jobs_placed(t, Sv.same(t), False{}), rp.known_same(r), rp.same(t))

def rp.same_new(js: List<&2, Sv.JRec>) -> {CronServe.sv_jobs_placed(js, List.append(&2, Sv.JOut, Sv.same(js), [Sv.JNew{}]), True{}) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case +r <> +t:
      rp.and_t(CronServe.sv_jplace(r, Sv.JSame{}), CronServe.sv_jobs_placed(t, List.append(&2, Sv.JOut, Sv.same(t), [Sv.JNew{}]), True{}), rp.known_same(r), rp.same_new(t))

def rp.recover(+ids: List<&2, Nat>, js: List<&2, Sv.JRec>) -> {CronServe.sv_jobs_placed(js, Sv.recover.jobs(ids, js), False{}) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          rp.recover(ids, t)
        case Sv.JKnown{i, f}:
          rp.recover(ids, t)

def rp.pick_fin(b: Bool, x: CS.Fin, i: Nat, f: CS.Fact) -> {CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.finish.pick(b, Sv.JFin{x})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.pick_cut(b: Bool, x: CS.Cut, i: Nat, f: CS.Fact) -> {CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.finish.pick(b, Sv.JCut{x})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.pick_again(b: Bool, x: CS.Again, i: Nat, f: CS.Fact) -> {CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.finish.pick(b, Sv.JAgain{x})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.finish(+j: Nat, +ran: Bool, +failed: Bool, +now: Nat, js: List<&2, Sv.JRec>) -> {CronServe.sv_jobs_placed(js, Sv.finish.jobs(j, ran, failed, now, js), False{}) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          rp.finish(j, ran, failed, now, t)
        case Sv.JKnown{+i, +f}:
          rp.and_t(CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.finish.pick(Nat.is_eq(i, j), Sv.JFin{CS.finish(CS.MINUTE(), f, ran, failed, now)})), CronServe.sv_jobs_placed(t, Sv.finish.jobs(j, ran, failed, now, t), False{}), rp.pick_fin(Nat.is_eq(i, j), CS.finish(CS.MINUTE(), f, ran, failed, now), i, f), rp.finish(j, ran, failed, now, t))

def rp.cancel(+n: Nat, js: List<&2, Sv.JRec>) -> {CronServe.sv_jobs_placed(js, Sv.cancel.jobs(n, js), False{}) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          rp.cancel(n, t)
        case Sv.JKnown{+i, +f}:
          rp.and_t(CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.finish.pick(Nat.is_eq(i, n), Sv.JCut{CS.cancel(f)})), CronServe.sv_jobs_placed(t, Sv.cancel.jobs(n, t), False{}), rp.pick_cut(Nat.is_eq(i, n), CS.cancel(f), i, f), rp.cancel(n, t))

def rp.resume(+n: Nat, +now: Nat, js: List<&2, Sv.JRec>) -> {CronServe.sv_jobs_placed(js, Sv.resume.jobs(n, now, js), False{}) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          rp.resume(n, now, t)
        case Sv.JKnown{+i, +f}:
          rp.and_t(CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.finish.pick(Nat.is_eq(i, n), Sv.JAgain{CS.resume(f, now)})), CronServe.sv_jobs_placed(t, Sv.resume.jobs(n, now, t), False{}), rp.pick_again(Nat.is_eq(i, n), CS.resume(f, now), i, f), rp.resume(n, now, t))

# The claim pass
# --------------

def rp.pj_put(o: Sv.JOut, p: Sv.Pass) -> {o <> rp.pj(p) == rp.pj(Sv.claim.put(o, p)) : List<&2, Sv.JOut>}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def rp.pj_add(b: Bool, +k: Nat, fresh: List<&2, String>, o: Sv.JOut, p: Sv.Pass) -> {o <> rp.pj(p) == rp.pj(Sv.claim.add(b, k, fresh, o, p)) : List<&2, Sv.JOut>}:
  match b fresh p:
    case True{} Nil{} Sv.Pass{jo, cn, ds}:
      {==}
    case True{} d <> r Sv.Pass{jo, cn, ds}:
      {==}
    case False{} _ Sv.Pass{jo, cn, ds}:
      {==}

def rp.pn_put(o: Sv.JOut, p: Sv.Pass) -> {rp.pn(p) == rp.pn(Sv.claim.put(o, p)) : List<&2, Sv.COut>}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def rp.pn_add(b: Bool, +k: Nat, fresh: List<&2, String>, o: Sv.JOut, p: Sv.Pass) -> {CronServe.sv_all_new(rp.pn(p)) == CronServe.sv_all_new(rp.pn(Sv.claim.add(b, k, fresh, o, p))) : Bool}:
  match b fresh p:
    case True{} Nil{} Sv.Pass{jo, cn, ds}:
      {==}
    case True{} d <> r Sv.Pass{jo, cn, ds}:
      {==}
    case False{} _ Sv.Pass{jo, cn, ds}:
      {==}

def rp.out(t: CS.Took, fresh: List<&2, String>, i: Nat, f: CS.Fact) -> {CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.claim.out(t, fresh)) == True{} : Bool}:
  match t fresh:
    case CS.Keep{} _:
      {==}
    case CS.Roll{n} _:
      {==}
    case CS.Claimed{n} Nil{}:
      {==}
    case CS.Claimed{n} d <> r:
      {==}

def rp.pass(js: List<&2, Sv.JRec>, +k: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat) -> {CronServe.sv_jobs_placed(js, rp.pj(Sv.claim(js, k, set, fresh, due, now)), False{}) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          %rp.pj_put(Sv.JSame{}, Sv.claim(t, 1n+k, set, fresh, due, now)) : {CronServe.sv_jobs_placed(Sv.JRaw{} <> t, _, False{}) == True{} : Bool}
          rp.pass(t, 1n+k, set, fresh, due, now)
        case Sv.JKnown{+i, +f}:
          +tk = CS.take(f, Cr.has(i, set), due, now)
          +b = Sv.claim.takes(tk, fresh)
          %rp.pj_add(b, k, fresh, Sv.claim.out(tk, fresh), Sv.claim(t, 1n+k, Sv.claim.set(b, i, set), Sv.claim.rest(b, fresh), due, now)) : {CronServe.sv_jobs_placed(Sv.JKnown{i, f} <> t, _, False{}) == True{} : Bool}
          rp.and_t(CronServe.sv_jplace(Sv.JKnown{i, f}, Sv.claim.out(tk, fresh)), CronServe.sv_jobs_placed(t, rp.pj(Sv.claim(t, 1n+k, Sv.claim.set(b, i, set), Sv.claim.rest(b, fresh), due, now)), False{}), rp.out(tk, fresh, i, f), rp.pass(t, 1n+k, Sv.claim.set(b, i, set), Sv.claim.rest(b, fresh), due, now))

def rp.news(js: List<&2, Sv.JRec>, +k: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat) -> {CronServe.sv_all_new(rp.pn(Sv.claim(js, k, set, fresh, due, now))) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          %rp.pn_put(Sv.JSame{}, Sv.claim(t, 1n+k, set, fresh, due, now)) : {CronServe.sv_all_new(_) == True{} : Bool}
          rp.news(t, 1n+k, set, fresh, due, now)
        case Sv.JKnown{+i, +f}:
          +tk = CS.take(f, Cr.has(i, set), due, now)
          +b = Sv.claim.takes(tk, fresh)
          %rp.pn_add(b, k, fresh, Sv.claim.out(tk, fresh), Sv.claim(t, 1n+k, Sv.claim.set(b, i, set), Sv.claim.rest(b, fresh), due, now)) : {_ == True{} : Bool}
          rp.news(t, 1n+k, Sv.claim.set(b, i, set), Sv.claim.rest(b, fresh), due, now)

# The claim answers
# -----------------

def rp.keep_c(c: Sv.CRec) -> {CronServe.sv_cplace(c, Sv.CKeep{}) == True{} : Bool}:
  match c:
    case Sv.CRaw{}:
      {==}
    case Sv.CKnown{d, j, o}:
      {==}

def rp.keep(cs: List<&2, Sv.CRec>) -> {CronServe.sv_claims_placed(cs, Sv.keep(cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      rp.and_t(CronServe.sv_cplace(c, Sv.CKeep{}), CronServe.sv_claims_placed(t, Sv.keep(t)), rp.keep_c(c), rp.keep(t))

def rp.keep_news(cs: List<&2, Sv.CRec>, +news: List<&2, Sv.COut>, all: {CronServe.sv_all_new(news) == True{} : Bool}) -> {CronServe.sv_claims_placed(cs, List.append(&2, Sv.COut, Sv.keep(cs), news)) == True{} : Bool}:
  match cs:
    case Nil{}:
      all
    case +c <> +t:
      rp.and_t(CronServe.sv_cplace(c, Sv.CKeep{}), CronServe.sv_claims_placed(t, List.append(&2, Sv.COut, Sv.keep(t), news)), rp.keep_c(c), rp.keep_news(t, news, all))

def rp.drop_c(b: Bool, d: String, j: Nat, o: Nat) -> {CronServe.sv_cplace(Sv.CKnown{d, j, o}, Sv.recover.claim(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.recover_c(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, c: Sv.CRec) -> {CronServe.sv_cplace(c, Sv.recover.claim(Sv.clears(me, runs, dead, c))) == True{} : Bool}:
  match c:
    case Sv.CRaw{}:
      {==}
    case Sv.CKnown{+d, +j, +o}:
      rp.drop_c(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o}), d, j, o)

def rp.recover_claims(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, Sv.CRec>) -> {CronServe.sv_claims_placed(cs, Sv.recover.claims(me, runs, dead, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      rp.and_t(CronServe.sv_cplace(c, Sv.recover.claim(Sv.clears(me, runs, dead, c))), CronServe.sv_claims_placed(t, Sv.recover.claims(me, runs, dead, t)), rp.recover_c(me, runs, dead, c), rp.recover_claims(me, runs, dead, t))

def rp.drop_pick(b: Bool, +x: String, +j: Nat, +o: Nat, +t: List<&2, Sv.CRec>, +r: List<&2, Sv.COut>, ih: {CronServe.sv_claims_placed(t, r) == True{} : Bool}) -> {CronServe.sv_claims_placed(Sv.CKnown{x, j, o} <> t, Sv.drop_first.pick(b, t, r)) == True{} : Bool}:
  match b:
    case True{}:
      rp.keep(t)
    case False{}:
      ih

def rp.drop_first(+d: String, cs: List<&2, Sv.CRec>) -> {CronServe.sv_claims_placed(cs, Sv.drop_first(d, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case Sv.CKnown{+x, +j, +o}:
          rp.drop_pick(String.eq(x, d), x, j, o, t, Sv.drop_first(d, t), rp.drop_first(d, t))
        case Sv.CRaw{}:
          rp.drop_first(d, t)

# Every update
# ------------

def rp.G(+js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, o: Sv.Out, create: Bool) -> Type:
  ({CronServe.sv_jobs_placed(js, CronServe.sv_jobs(o), create) == True{} : Bool} & {CronServe.sv_claims_placed(cs, CronServe.sv_claims_out(o)) == True{} : Bool})

def rp.unchanged(aside: Bool, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> rp.G(js, cs, Sv.Out{aside, False{}, Sv.same(js), Sv.keep(cs)}, False{}):
  (rp.same(js), rp.keep(cs))

def rp.own(own: Bool, +j: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> rp.G(js, cs, Sv.finish.own(own, False{}, j, d, ran, failed, now, js, cs), False{}):
  match own:
    case True{}:
      (rp.finish(j, ran, failed, now, js), rp.drop_first(d, cs))
    case False{}:
      rp.unchanged(False{}, js, cs)

def rp.found(m: Maybe<&2, Sv.Hit>, +me: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> rp.G(js, cs, Sv.finish.found(m, me, False{}, d, ran, failed, now, js, cs), False{}):
  match m:
    case None{}:
      rp.unchanged(False{}, js, cs)
    case Some{p}:
      match p:
        case Sv.Hit{+j, +o}:
          rp.own(Nat.is_eq(o, me), j, d, ran, failed, now, js, cs)

def rp.finish_run(b: Bool, +me: Nat, +runs: List<&2, String>, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> rp.G(js, cs, CronServe.sv_reply(Sv.finish(b, me, runs, False{}, d, ran, failed, now, js, cs)), False{}):
  match b:
    case True{}:
      rp.found(Sv.claim_of(d, cs), me, d, ran, failed, now, js, cs)
    case False{}:
      rp.unchanged(False{}, js, cs)

def rp.claim_end(+runs: List<&2, String>, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, p: Sv.Pass, pj: {CronServe.sv_jobs_placed(js, rp.pj(p), False{}) == True{} : Bool}, pn: {CronServe.sv_all_new(rp.pn(p)) == True{} : Bool}) -> rp.G(js, cs, CronServe.sv_reply(Sv.claim.end(False{}, runs, cs, p)), False{}):
  match p:
    case Sv.Pass{jo, +cn, ds}:
      (pj, rp.keep_news(cs, cn, pn))

def rp.go(+runs: List<&2, String>, +me: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, op: Sv.Op) -> rp.G(js, cs, CronServe.sv_reply(Sv.go(runs, me, False{}, js, cs, op)), CronServe.sv_is_create(op)):
  match op:
    case Sv.OClaim{+due, +now, +fresh}:
      rp.claim_end(runs, js, cs, Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now), rp.pass(js, 0n, Sv.claim_jobs(cs), fresh, due, now), rp.news(js, 0n, Sv.claim_jobs(cs), fresh, due, now))
    case Sv.ORecover{+dead}:
      (rp.recover(Sv.cleared(me, runs, dead, cs), js), rp.recover_claims(me, runs, dead, cs))
    case Sv.OFinish{+d, +ran, +failed, +now}:
      rp.finish_run(Sv.has_str(d, runs), me, runs, d, ran, failed, now, js, cs)
    case Sv.OCancel{+n}:
      (rp.cancel(n, js), rp.keep(cs))
    case Sv.OResume{+n, +now}:
      (rp.resume(n, now, js), rp.keep(cs))
    case Sv.OCreate{n, f}:
      (rp.same_new(js), rp.keep(cs))

def CronServe.cron_serve_records_in_place(runs, me, js, cs, op):
  rp.go(runs, me, js, cs, op)
