# eukhe: the proof of LAW cron_serve_claims_unclaimed
# A claim pass keeps every claim record, then makes its new claims. The
# pass walks the job records from position k (the records past k of the
# file); it claims the known job at k only when the decision on it is a
# claim, which the decision answers only for a job with no claim in the
# pass's set; the set starts as the jobs of the claims on record and gains
# each job claimed, exactly as the law's `taken` does.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ./base/exact.bend as LSx
import ./base/logic.bend as LG

# The file from position k
# ------------------------

# xs without its first k elements
def cu.drop(-A: Data, k: Nat, xs: List<&2, A>) -> List<&2, A>:
  match k xs:
    case 0n _:
      xs
    case 1n+p Nil{}:
      Nil{}
    case 1n+p h <> t:
      cu.drop(A, p, t)

def cu.isc(-A: Data, xs: List<&2, A>, G: Type) -> Type:
  match xs:
    case Nil{}:
      G
    case h <> t:
      Unit

def cu.nil_cons(-A: Data, -r: A, -t: List<&2, A>, -G: Type, e: {Nil{} == r <> t : List<&2, A>}) -> G:
  %Equal.sym(List<&2, A>, Nil{}, r <> t, e) : cu.isc(A, _, G)
  Unit{}

# the element at k is the first of the list from k
def cu.drop_get(-A: Data, k: Nat, xs: List<&2, A>, -r: A, -t: List<&2, A>, e: {cu.drop(A, k, xs) == r <> t : List<&2, A>}) -> {List.get(&2, A, xs, k) == Some{r} : Maybe<&2, A>}:
  match k xs:
    case 0n _:
      %Equal.sym(List<&2, A>, xs, r <> t, e) : {List.get(&2, A, _, 0n) == Some{r} : Maybe<&2, A>}
      {==}
    case 1n+p Nil{}:
      cu.nil_cons(A, r, t, {List.get(&2, A, Nil{}, 1n+p) == Some{r} : Maybe<&2, A>}, e)
    case 1n+p h <> u:
      cu.drop_get(A, p, u, r, t, e)

# the list from 1+k is the rest of the list from k
def cu.drop_next(-A: Data, k: Nat, xs: List<&2, A>, -r: A, -t: List<&2, A>, e: {cu.drop(A, k, xs) == r <> t : List<&2, A>}) -> {cu.drop(A, 1n+k, xs) == t : List<&2, A>}:
  match k xs:
    case 0n _:
      %Equal.sym(List<&2, A>, xs, r <> t, e) : {cu.drop(A, 1n, _) == t : List<&2, A>}
      {==}
    case 1n+p Nil{}:
      cu.nil_cons(A, r, t, {cu.drop(A, 2n+p, Nil{}) == t : List<&2, A>}, e)
    case 1n+p h <> u:
      cu.drop_next(A, p, u, r, t, e)

# The decision claims only an unclaimed job
# -----------------------------------------

def cu.tk(t: CS.Took, G: Type) -> Type:
  match t:
    case CS.Keep{}:
      G
    case CS.Roll{n}:
      G
    case CS.Claimed{n}:
      Unit

def cu.keep_claim(-n: CS.Next, -G: Type, e: {CS.Keep{} == CS.Claimed{n} : CS.Took}) -> G:
  %Equal.sym(CS.Took, CS.Keep{}, CS.Claimed{n}, e) : cu.tk(_, G)
  Unit{}

def cu.roll_claim(-m: CS.Next, -n: CS.Next, -G: Type, e: {CS.Roll{m} == CS.Claimed{n} : CS.Took}) -> G:
  %Equal.sym(CS.Took, CS.Roll{m}, CS.Claimed{n}, e) : cu.tk(_, G)
  Unit{}

def cu.ud(dueb: Bool, c: Bool, p: CS.Plan, +now: Nat, -n: CS.Next, e: {CS.take.due(dueb, c, p, now) == CS.Claimed{n} : CS.Took}) -> {c == False{} : Bool}:
  match dueb c:
    case False{} _:
      cu.keep_claim(n, {c == False{} : Bool}, e)
    case True{} True{}:
      cu.roll_claim(CS.roll(p, now), n, {True{} == False{} : Bool}, e)
    case True{} False{}:
      {==}

def cu.un(nx: Maybe<&2, Nat>, +due: Nat, c: Bool, p: CS.Plan, +now: Nat, -n: CS.Next, e: {CS.take.next(nx, due, c, p, now) == CS.Claimed{n} : CS.Took}) -> {c == False{} : Bool}:
  match nx:
    case None{}:
      cu.keep_claim(n, {c == False{} : Bool}, e)
    case Some{m}:
      cu.ud(Nat.is_le(m, due), c, p, now, n, e)

# a claim answer means no claim of the job was on record
def cu.unclaimed(f: CS.Fact, c: Bool, +due: Nat, +now: Nat, -n: CS.Next, e: {CS.take(f, c, due, now) == CS.Claimed{n} : CS.Took}) -> {c == False{} : Bool}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          cu.un(nx, due, c, p, now, n, e)
        case Cr.Paused{}:
          cu.keep_claim(n, {c == False{} : Bool}, e)
        case Cr.Finished{}:
          cu.keep_claim(n, {c == False{} : Bool}, e)
        case Cr.Cancelled{}:
          cu.keep_claim(n, {c == False{} : Bool}, e)

# The pass
# --------

def cu.news(p: Sv.Pass) -> List<&2, Sv.COut>:
  match p:
    case Sv.Pass{jo, cn, ds}:
      cn

def cu.news_put(o: Sv.JOut, p: Sv.Pass) -> {cu.news(Sv.claim.put(o, p)) == cu.news(p) : List<&2, Sv.COut>}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def cu.news_new(+k: Nat, +d: String, o: Sv.JOut, p: Sv.Pass) -> {cu.news(Sv.claim.new(k, d, o, p)) == Sv.CNew{k, d} <> cu.news(p) : List<&2, Sv.COut>}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

# one known job at k: a claim of it is of a job not in the set
def cu.at(tk: CS.Took, +i: Nat, f: CS.Fact, +k: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat, +full: List<&2, Sv.JRec>, +t: List<&2, Sv.JRec>,
  etk: {CS.take(f, Cr.has(i, set), due, now) == tk : CS.Took},
  ef: {List.get(&2, Sv.JRec, full, k) == Some{Sv.JKnown{i, f}} : Maybe<&2, Sv.JRec>},
  ih: {CronServe.sv_new_unclaimed(cu.news(Sv.claim(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now)), full, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set)) == True{} : Bool}) -> {CronServe.sv_new_unclaimed(cu.news(Sv.claim.add(Sv.claim.takes(tk, fresh), k, fresh, Sv.claim.out(tk, fresh), Sv.claim(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now))), full, set) == True{} : Bool}:
  match tk fresh:
    case CS.Keep{} _:
      %Equal.sym(List<&2, Sv.COut>, cu.news(Sv.claim.put(Sv.JTook{CS.Keep{}}, Sv.claim(t, 1n+k, set, fresh, due, now))), cu.news(Sv.claim(t, 1n+k, set, fresh, due, now)), cu.news_put(Sv.JTook{CS.Keep{}}, Sv.claim(t, 1n+k, set, fresh, due, now))) : {CronServe.sv_new_unclaimed(_, full, set) == True{} : Bool}
      ih
    case CS.Roll{n} _:
      %Equal.sym(List<&2, Sv.COut>, cu.news(Sv.claim.put(Sv.JTook{CS.Roll{n}}, Sv.claim(t, 1n+k, set, fresh, due, now))), cu.news(Sv.claim(t, 1n+k, set, fresh, due, now)), cu.news_put(Sv.JTook{CS.Roll{n}}, Sv.claim(t, 1n+k, set, fresh, due, now))) : {CronServe.sv_new_unclaimed(_, full, set) == True{} : Bool}
      ih
    case CS.Claimed{n} Nil{}:
      %Equal.sym(List<&2, Sv.COut>, cu.news(Sv.claim.put(Sv.JSame{}, Sv.claim(t, 1n+k, set, Nil{}, due, now))), cu.news(Sv.claim(t, 1n+k, set, Nil{}, due, now)), cu.news_put(Sv.JSame{}, Sv.claim(t, 1n+k, set, Nil{}, due, now))) : {CronServe.sv_new_unclaimed(_, full, set) == True{} : Bool}
      ih
    case CS.Claimed{n} +d <> r:
      +p = Sv.claim(t, 1n+k, i <> set, r, due, now)
      %Equal.sym(List<&2, Sv.COut>, cu.news(Sv.claim.new(k, d, Sv.JTook{CS.Claimed{n}}, p)), Sv.CNew{k, d} <> cu.news(p), cu.news_new(k, d, Sv.JTook{CS.Claimed{n}}, p)) : {CronServe.sv_new_unclaimed(_, full, set) == True{} : Bool}
      %Equal.sym(Maybe<&2, Sv.JRec>, List.get(&2, Sv.JRec, full, k), Some{Sv.JKnown{i, f}}, ef) : {Bool.and(CronServe.sv_new.ok(CronServe.sv_job_of(_), set), CronServe.sv_new_unclaimed(cu.news(p), full, CronServe.sv_new.add(CronServe.sv_job_of(_), set))) == True{} : Bool}
      %LSx.sx.has(i, set) : {Bool.and(Bool.not(_), CronServe.sv_new_unclaimed(cu.news(p), full, i <> set)) == True{} : Bool}
      %Equal.sym(Bool, Cr.has(i, set), False{}, cu.unclaimed(f, Cr.has(i, set), due, now, n, etk)) : {Bool.and(Bool.not(_), CronServe.sv_new_unclaimed(cu.news(p), full, i <> set)) == True{} : Bool}
      ih

# the pass over the records from position k makes only claims of known
# jobs not in the set
def cu.pass(t: List<&2, Sv.JRec>, +k: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat, +full: List<&2, Sv.JRec>, +sfx: {cu.drop(Sv.JRec, k, full) == t : List<&2, Sv.JRec>}) -> {CronServe.sv_new_unclaimed(cu.news(Sv.claim(t, k, set, fresh, due, now)), full, set) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case r <> +t2:
      match r:
        case Sv.JRaw{}:
          %Equal.sym(List<&2, Sv.COut>, cu.news(Sv.claim.put(Sv.JSame{}, Sv.claim(t2, 1n+k, set, fresh, due, now))), cu.news(Sv.claim(t2, 1n+k, set, fresh, due, now)), cu.news_put(Sv.JSame{}, Sv.claim(t2, 1n+k, set, fresh, due, now))) : {CronServe.sv_new_unclaimed(_, full, set) == True{} : Bool}
          cu.pass(t2, 1n+k, set, fresh, due, now, full, cu.drop_next(Sv.JRec, k, full, Sv.JRaw{}, t2, sfx))
        case Sv.JKnown{+i, +f}:
          +tk = CS.take(f, Cr.has(i, set), due, now)
          +b = Sv.claim.takes(tk, fresh)
          cu.at(tk, i, f, k, set, fresh, due, now, full, t2, {==}, cu.drop_get(Sv.JRec, k, full, Sv.JKnown{i, f}, t2, sfx), cu.pass(t2, 1n+k, Sv.claim.set(b, i, set), Sv.claim.rest(b, fresh), due, now, full, cu.drop_next(Sv.JRec, k, full, Sv.JKnown{i, f}, t2, sfx)))

# The answer
# ----------

def cu.keep_skip(cs: List<&2, Sv.CRec>, +cn: List<&2, Sv.COut>, +js: List<&2, Sv.JRec>, +taken: List<&2, Nat>) -> {CronServe.sv_new_unclaimed(List.append(&2, Sv.COut, Sv.keep(cs), cn), js, taken) == CronServe.sv_new_unclaimed(cn, js, taken) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      cu.keep_skip(t, cn, js, taken)

def cu.end(+runs: List<&2, String>, +cs: List<&2, Sv.CRec>, p: Sv.Pass, +js: List<&2, Sv.JRec>, +taken: List<&2, Nat>) -> {CronServe.sv_new_unclaimed(CronServe.sv_claims_out(CronServe.sv_reply(Sv.claim.end(False{}, runs, cs, p))), js, taken) == CronServe.sv_new_unclaimed(cu.news(p), js, taken) : Bool}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      cu.keep_skip(cs, cn, js, taken)

def CronServe.cron_serve_claims_unclaimed(runs, me, js, cs, due, now, fresh):
  +p = Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now)
  +e = cu.end(runs, cs, p, js, CronServe.sv_taken(cs))
  %Equal.sym(Bool, CronServe.sv_new_unclaimed(CronServe.sv_claims_out(CronServe.sv_reply(Sv.claim.end(False{}, runs, cs, p))), js, CronServe.sv_taken(cs)), CronServe.sv_new_unclaimed(cu.news(p), js, CronServe.sv_taken(cs)), e) : {_ == True{} : Bool}
  %LSx.sx.taken(cs) : {CronServe.sv_new_unclaimed(cu.news(p), js, _) == True{} : Bool}
  cu.pass(js, 0n, Sv.claim_jobs(cs), fresh, due, now, js, {==})
