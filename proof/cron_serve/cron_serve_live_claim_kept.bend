# eukhe: the proof of LAW cron_serve_live_claim_kept
# A claim pass, a cancel, a resume and a create keep every claim record
# (their claim answers start with one keep per record). A recovery answers
# each claim record with the verdict on it, and the verdict on a live claim
# (this process's that it runs, another live process's) keeps it. A finish
# drops at most the first known claim of its dispatch, and only when this
# process owns that claim: a claim this process owns of a dispatch it runs
# that is not the finished one is not that claim, and another's claim at
# that place would be the first and owned by another (no drop at all).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ./base/exact.bend as LSx
import ./base/logic.bend as LG

# Lists
# -----

def lk.val(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def lk.some_inj(-A: Data, a: A, b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  %e : {a == lk.val(A, a, _) : A}
  {==}

def lk.isn(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def lk.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %Equal.sym(Maybe<&2, A>, None{}, Some{x}, e) : lk.isn(A, _, G)
  Unit{}

def lk.is_known(c: Sv.CRec, G: Type) -> Type:
  match c:
    case Sv.CKnown{d, j, o}:
      Unit
    case Sv.CRaw{}:
      G

def lk.raw_known(-d: String, -j: Nat, -o: Nat, -G: Type, e: {Sv.CRaw{} == Sv.CKnown{d, j, o} : Sv.CRec}) -> G:
  %Equal.sym(Sv.CRec, Sv.CRaw{}, Sv.CKnown{d, j, o}, e) : lk.is_known(_, G)
  Unit{}

def lk.cid(c: Sv.CRec) -> String:
  match c:
    case Sv.CKnown{d, j, o}:
      d
    case Sv.CRaw{}:
      ""

def lk.cown(c: Sv.CRec) -> Nat:
  match c:
    case Sv.CKnown{d, j, o}:
      o
    case Sv.CRaw{}:
      0n

def lk.hown(h: Sv.Hit) -> Nat:
  match h:
    case Sv.Hit{j, o}:
      o

# every claim record keeps its place: a keep at every record's position
def lk.keep_at(cs: List<&2, Sv.CRec>, +news: List<&2, Sv.COut>, k: Nat, -c: Sv.CRec, at: {List.get(&2, Sv.CRec, cs, k) == Some{c} : Maybe<&2, Sv.CRec>}) -> {List.get(&2, Sv.COut, List.append(&2, Sv.COut, Sv.keep(cs), news), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match cs k:
    case Nil{} _:
      lk.none_some(Sv.CRec, c, {List.get(&2, Sv.COut, news, k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}, at)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      lk.keep_at(t, news, p, c, at)

def lk.keep_at0(cs: List<&2, Sv.CRec>, k: Nat, -c: Sv.CRec, at: {List.get(&2, Sv.CRec, cs, k) == Some{c} : Maybe<&2, Sv.CRec>}) -> {List.get(&2, Sv.COut, Sv.keep(cs), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match cs k:
    case Nil{} _:
      lk.none_some(Sv.CRec, c, {List.get(&2, Sv.COut, Nil{}, k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}, at)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      lk.keep_at0(t, p, c, at)

# a recovery answers each claim record with the verdict on it
def lk.rec_at(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, Sv.CRec>, k: Nat, +c: Sv.CRec, at: {List.get(&2, Sv.CRec, cs, k) == Some{c} : Maybe<&2, Sv.CRec>}) -> {List.get(&2, Sv.COut, Sv.recover.claims(me, runs, dead, cs), k) == Some{Sv.recover.claim(Sv.clears(me, runs, dead, c))} : Maybe<&2, Sv.COut>}:
  match cs k:
    case Nil{} _:
      lk.none_some(Sv.CRec, c, {List.get(&2, Sv.COut, Nil{}, k) == Some{Sv.recover.claim(Sv.clears(me, runs, dead, c))} : Maybe<&2, Sv.COut>}, at)
    case +h <> t 0n:
      +e = lk.some_inj(Sv.CRec, h, c, at)
      %e : {Some{Sv.recover.claim(Sv.clears(me, runs, dead, h))} == Some{Sv.recover.claim(Sv.clears(me, runs, dead, _))} : Maybe<&2, Sv.COut>}
      {==}
    case h <> t 1n+p:
      lk.rec_at(me, runs, dead, t, p, c, at)

# The verdict on a live claim keeps it
# ------------------------------------

def lk.not_t(+b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LG.lg.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def lk.stays_rec.own(own: Bool, +me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +d: String, +o: Nat, stays: {CronServe.sv_stays.own(own, CronServe.sv_in(d, runs), Bool.not(CronServe.sv_has(o, dead))) == True{} : Bool}) -> {Sv.recover.claim(CS.clear(Sv.who(own, d, o, runs, dead))) == Sv.CKeep{} : Sv.COut}:
  match own:
    case True{}:
      %Equal.sym(Bool, Sv.has_str(d, runs), CronServe.sv_in(d, runs), LSx.sx.in(d, runs)) : {Sv.recover.claim(Bool.not(_)) == Sv.CKeep{} : Sv.COut}
      %Equal.sym(Bool, CronServe.sv_in(d, runs), True{}, stays) : {Sv.recover.claim(Bool.not(_)) == Sv.CKeep{} : Sv.COut}
      {==}
    case False{}:
      %Equal.sym(Bool, Cr.has(o, dead), CronServe.sv_has(o, dead), LSx.sx.has(o, dead)) : {Sv.recover.claim(_) == Sv.CKeep{} : Sv.COut}
      %Equal.sym(Bool, CronServe.sv_has(o, dead), False{}, lk.not_t(CronServe.sv_has(o, dead), stays)) : {Sv.recover.claim(_) == Sv.CKeep{} : Sv.COut}
      {==}

# Finish: the drop is only at the first claim of the dispatch, owned here
# -----------------------------------------------------------------------

# the first known claim of x, at position 0 of CKnown{d0, j0, o0} <> t, is
# dropped only when its id is x; then it is the claim the finish found
def lk.d0(b: Bool, +x: String, +d: String, +j: Nat, +o: Nat, +d0: String, +j0: Nat, +o0: Nat, +me: Nat, +t: List<&2, Sv.CRec>, -j1: Nat, +o1: Nat,
  eb: {String.eq(d0, x) == b : Bool},
  +at: {Sv.CKnown{d0, j0, o0} == Sv.CKnown{d, j, o} : Sv.CRec},
  first: {Sv.claim_of.pick(b, j0, o0, Sv.claim_of(x, t)) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>},
  mine: {Nat.is_eq(o1, me) == True{} : Bool},
  ne: {Bool.and(Nat.is_eq(o, me), String.eq(d, x)) == False{} : Bool}) -> {List.get(&2, Sv.COut, Sv.drop_first.pick(b, t, Sv.drop_first(x, t)), 0n) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match b:
    case True{}:
      +eo = Equal.trans(Nat, o, o0, o1, Equal.cong(Sv.CRec, Nat, c => lk.cown(c), Sv.CKnown{d, j, o}, Sv.CKnown{d0, j0, o0}, Equal.sym(Sv.CRec, Sv.CKnown{d0, j0, o0}, Sv.CKnown{d, j, o}, at)), Equal.cong(Maybe<&2, Sv.Hit>, Nat, m => lk.hown(lk.val(Sv.Hit, Sv.Hit{0n, 0n}, m)), Some{Sv.Hit{j0, o0}}, Some{Sv.Hit{j1, o1}}, first))
      +ed = Equal.cong(Sv.CRec, String, c => lk.cid(c), Sv.CKnown{d, j, o}, Sv.CKnown{d0, j0, o0}, Equal.sym(Sv.CRec, Sv.CKnown{d0, j0, o0}, Sv.CKnown{d, j, o}, at))
      +h1 = Equal.trans(Bool, Nat.is_eq(o, me), Nat.is_eq(o1, me), True{}, Equal.cong(Nat, Bool, n => Nat.is_eq(n, me), o, o1, eo), mine)
      +h2 = Equal.trans(Bool, String.eq(d, x), String.eq(d0, x), True{}, Equal.cong(String, Bool, s => String.eq(s, x), d, d0, ed), eb)
      +h = LG.lg.and_t(Nat.is_eq(o, me), String.eq(d, x), h1, h2)
      LG.lg.tf({List.get(&2, Sv.COut, Sv.CDrop{} <> Sv.keep(t), 0n) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}, Equal.trans(Bool, True{}, Bool.and(Nat.is_eq(o, me), String.eq(d, x)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(o, me), String.eq(d, x)), True{}, h), ne))
    case False{}:
      {==}

def lk.drop0(c: Sv.CRec, +x: String, +d: String, +j: Nat, +o: Nat, +me: Nat, +t: List<&2, Sv.CRec>, -j1: Nat, +o1: Nat,
  at: {Some{c} == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>},
  first: {Sv.claim_of(x, c <> t) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>},
  mine: {Nat.is_eq(o1, me) == True{} : Bool},
  ne: {Bool.and(Nat.is_eq(o, me), String.eq(d, x)) == False{} : Bool}) -> {List.get(&2, Sv.COut, Sv.drop_first(x, c <> t), 0n) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match c:
    case Sv.CRaw{}:
      lk.raw_known(d, j, o, {List.get(&2, Sv.COut, Sv.drop_first(x, Sv.CRaw{} <> t), 0n) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}, lk.some_inj(Sv.CRec, Sv.CRaw{}, Sv.CKnown{d, j, o}, at))
    case Sv.CKnown{+d0, +j0, +o0}:
      lk.d0(String.eq(d0, x), x, d, j, o, d0, j0, o0, me, t, j1, o1, {==}, lk.some_inj(Sv.CRec, Sv.CKnown{d0, j0, o0}, Sv.CKnown{d, j, o}, at), first, mine, ne)

def lk.dk(b: Bool, +x: String, +t: List<&2, Sv.CRec>, +p: Nat, -j0: Nat, -o0: Nat, -d: String, -j: Nat, -o: Nat, -j1: Nat, -o1: Nat,
  first: {Sv.claim_of.pick(b, j0, o0, Sv.claim_of(x, t)) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>},
  at: {List.get(&2, Sv.CRec, t, p) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>},
  ih: {Sv.claim_of(x, t) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>} -> {List.get(&2, Sv.COut, Sv.drop_first(x, t), p) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}) -> {List.get(&2, Sv.COut, Sv.drop_first.pick(b, t, Sv.drop_first(x, t)), 1n+p) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match b:
    case True{}:
      lk.keep_at0(t, p, Sv.CKnown{d, j, o}, at)
    case False{}:
      ih(first)

def lk.dS(c: Sv.CRec, +x: String, +t: List<&2, Sv.CRec>, +p: Nat, -d: String, -j: Nat, -o: Nat, -j1: Nat, -o1: Nat,
  first: {Sv.claim_of(x, c <> t) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>},
  at: {List.get(&2, Sv.CRec, t, p) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>},
  ih: {Sv.claim_of(x, t) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>} -> {List.get(&2, Sv.COut, Sv.drop_first(x, t), p) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}) -> {List.get(&2, Sv.COut, Sv.drop_first(x, c <> t), 1n+p) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match c:
    case Sv.CRaw{}:
      ih(first)
    case Sv.CKnown{+d0, j0, o0}:
      lk.dk(String.eq(d0, x), x, t, p, j0, o0, d, j, o, j1, o1, first, at, ih)

# the finish drops no claim at k: the first known claim of x is owned
# here (mine), and the claim at k is not owned here or has another id (ne)
def lk.drop(cs: List<&2, Sv.CRec>, k: Nat, +x: String, +d: String, +j: Nat, +o: Nat, +me: Nat, -j1: Nat, +o1: Nat,
  +at: {List.get(&2, Sv.CRec, cs, k) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>},
  first: {Sv.claim_of(x, cs) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>},
  +mine: {Nat.is_eq(o1, me) == True{} : Bool},
  +ne: {Bool.and(Nat.is_eq(o, me), String.eq(d, x)) == False{} : Bool}) -> {List.get(&2, Sv.COut, Sv.drop_first(x, cs), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match cs k:
    case Nil{} _:
      lk.none_some(Sv.CRec, Sv.CKnown{d, j, o}, {List.get(&2, Sv.COut, Sv.drop_first(x, Nil{}), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}, at)
    case c <> +t 0n:
      lk.drop0(c, x, d, j, o, me, t, j1, o1, at, first, mine, ne)
    case c <> +t 1n++p:
      lk.dS(c, x, t, p, d, j, o, j1, o1, first, at, e => lk.drop(t, p, x, d, j, o, me, j1, o1, at, e, mine, ne))

# a claim owned here of a dispatch this process runs, with the finish of
# x: it is not the finished claim (stays), so ne holds
def lk.ne2(oo: Bool, sdx: Bool, +x: String, +d: String, +runs: List<&2, String>,
  ed: {String.eq(d, x) == sdx : Bool},
  run: {Sv.has_str(x, runs) == True{} : Bool},
  stays: {CronServe.sv_stays.own(oo, Bool.or(Bool.not(CronServe.sv_in(d, runs)), Bool.not(String.eq(x, d))), True{}) == True{} : Bool}) -> {Bool.and(oo, sdx) == False{} : Bool}:
  match oo sdx:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      +edx = LG.lg.str_sound(d, x, ed)
      +hin = Equal.trans(Bool, CronServe.sv_in(d, runs), CronServe.sv_in(x, runs), True{}, Equal.cong(String, Bool, s => CronServe.sv_in(s, runs), d, x, edx), Equal.trans(Bool, CronServe.sv_in(x, runs), Sv.has_str(x, runs), True{}, Equal.sym(Bool, Sv.has_str(x, runs), CronServe.sv_in(x, runs), LSx.sx.in(x, runs)), run))
      +hxd = Equal.trans(Bool, String.eq(x, d), String.eq(x, x), True{}, Equal.cong(String, Bool, s => String.eq(x, s), d, x, edx), LG.lg.str_refl(x))
      +h1 = Equal.cong(Bool, Bool, a => Bool.or(Bool.not(a), Bool.not(String.eq(x, d))), CronServe.sv_in(d, runs), True{}, hin)
      +h2 = Equal.cong(Bool, Bool, a => Bool.not(a), String.eq(x, d), True{}, hxd)
      LG.lg.tf({Bool.and(True{}, True{}) == False{} : Bool}, Equal.trans(Bool, True{}, Bool.or(Bool.not(CronServe.sv_in(d, runs)), Bool.not(String.eq(x, d))), False{}, Equal.sym(Bool, Bool.or(Bool.not(CronServe.sv_in(d, runs)), Bool.not(String.eq(x, d))), True{}, stays), Equal.trans(Bool, Bool.or(Bool.not(CronServe.sv_in(d, runs)), Bool.not(String.eq(x, d))), Bool.not(String.eq(x, d)), False{}, h1, h2)))

def lk.ne(+o: Nat, +me: Nat, +x: String, +d: String, +runs: List<&2, String>,
  run: {Sv.has_str(x, runs) == True{} : Bool},
  stays: {CronServe.sv_stays.own(Nat.is_eq(o, me), Bool.or(Bool.not(CronServe.sv_in(d, runs)), Bool.not(String.eq(x, d))), True{}) == True{} : Bool}) -> {Bool.and(Nat.is_eq(o, me), String.eq(d, x)) == False{} : Bool}:
  lk.ne2(Nat.is_eq(o, me), String.eq(d, x), x, d, runs, {==}, run, stays)

# The finish's branches
# ---------------------

def lk.own(own: Bool, +me: Nat, +x: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, +k: Nat, +d: String, +j: Nat, +o: Nat, -j1: Nat, +o1: Nat,
  mine: {Nat.is_eq(o1, me) == own : Bool},
  at: {List.get(&2, Sv.CRec, cs, k) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>},
  first: {Sv.claim_of(x, cs) == Some{Sv.Hit{j1, o1}} : Maybe<&2, Sv.Hit>},
  ne: {Bool.and(Nat.is_eq(o, me), String.eq(d, x)) == False{} : Bool}) -> {List.get(&2, Sv.COut, CronServe.sv_claims_out(Sv.finish.own(own, False{}, j1, x, ran, failed, now, js, cs)), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match own:
    case True{}:
      lk.drop(cs, k, x, d, j, o, me, j1, o1, at, first, mine, ne)
    case False{}:
      lk.keep_at0(cs, k, Sv.CKnown{d, j, o}, at)

def lk.found(m: Maybe<&2, Sv.Hit>, +me: Nat, +x: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, +k: Nat, +d: String, +j: Nat, +o: Nat,
  em: {Sv.claim_of(x, cs) == m : Maybe<&2, Sv.Hit>},
  at: {List.get(&2, Sv.CRec, cs, k) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>},
  ne: {Bool.and(Nat.is_eq(o, me), String.eq(d, x)) == False{} : Bool}) -> {List.get(&2, Sv.COut, CronServe.sv_claims_out(Sv.finish.found(m, me, False{}, x, ran, failed, now, js, cs)), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match m:
    case None{}:
      lk.keep_at0(cs, k, Sv.CKnown{d, j, o}, at)
    case Some{p}:
      match p:
        case Sv.Hit{j1, +o1}:
          lk.own(Nat.is_eq(o1, me), me, x, ran, failed, now, js, cs, k, d, j, o, j1, o1, {==}, at, em, ne)

def lk.fin(b: Bool, +me: Nat, +runs: List<&2, String>, +x: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, +k: Nat, +d: String, +j: Nat, +o: Nat,
  eb: {Sv.has_str(x, runs) == b : Bool},
  at: {List.get(&2, Sv.CRec, cs, k) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>},
  stays: {CronServe.sv_stays.own(Nat.is_eq(o, me), Bool.or(Bool.not(CronServe.sv_in(d, runs)), Bool.not(String.eq(x, d))), True{}) == True{} : Bool}) -> {List.get(&2, Sv.COut, CronServe.sv_claims_out(CronServe.sv_reply(Sv.finish(b, me, runs, False{}, x, ran, failed, now, js, cs))), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match b:
    case True{}:
      lk.found(Sv.claim_of(x, cs), me, x, ran, failed, now, js, cs, k, d, j, o, {==}, at, lk.ne(o, me, x, d, runs, eb, stays))
    case False{}:
      lk.keep_at0(cs, k, Sv.CKnown{d, j, o}, at)

def lk.claim_end(+runs: List<&2, String>, +cs: List<&2, Sv.CRec>, p: Sv.Pass, +k: Nat, -c: Sv.CRec, at: {List.get(&2, Sv.CRec, cs, k) == Some{c} : Maybe<&2, Sv.CRec>}) -> {List.get(&2, Sv.COut, CronServe.sv_claims_out(CronServe.sv_reply(Sv.claim.end(False{}, runs, cs, p))), k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}:
  match p:
    case Sv.Pass{jo, +cn, ds}:
      lk.keep_at(cs, cn, k, c, at)

def CronServe.cron_serve_live_claim_kept(runs, me, js, cs, op, k, d, j, o, at, stays):
  match op:
    case Sv.OClaim{+due, +now, +fresh}:
      lk.claim_end(runs, cs, Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now), k, Sv.CKnown{d, j, o}, at)
    case Sv.ORecover{+dead}:
      Equal.trans(Maybe<&2, Sv.COut>, List.get(&2, Sv.COut, Sv.recover.claims(me, runs, dead, cs), k), Some{Sv.recover.claim(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o}))}, Some{Sv.CKeep{}}, lk.rec_at(me, runs, dead, cs, k, Sv.CKnown{d, j, o}, at), Equal.cong(Sv.COut, Maybe<&2, Sv.COut>, v => Some{v}, Sv.recover.claim(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o})), Sv.CKeep{}, lk.stays_rec.own(Nat.is_eq(o, me), me, runs, dead, d, o, stays)))
    case Sv.OFinish{+x, +ran, +failed, +now}:
      lk.fin(Sv.has_str(x, runs), me, runs, x, ran, failed, now, js, cs, k, d, j, o, {==}, at, stays)
    case Sv.OCancel{n}:
      lk.keep_at0(cs, k, Sv.CKnown{d, j, o}, at)
    case Sv.OResume{n, now}:
      lk.keep_at0(cs, k, Sv.CKnown{d, j, o}, at)
    case Sv.OCreate{n, f}:
      lk.keep_at0(cs, k, Sv.CKnown{d, j, o}, at)
