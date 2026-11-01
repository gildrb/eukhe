# eukhe: lemmas the proofs of area cron_serve share: every part of the
# serve the stepper runs (bend/cron_serve.bend) is the spec's
# (laws/cron_serve/serve.bend), part by part: the small parts by a case
# split, the walks over the records by induction, each per-job decision by
# its cron_store law (cron_take_exact, cron_clear_exact, ...).

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/cron_serve.bend as Sv
import ../../../laws/cron_store.bend as CronStore
import ../../../laws/cron_serve/serve.bend as CronServe
import ../../cron_store/cron_take_exact.bend as PX0
import ../../cron_store/cron_clear_exact.bend as PX1
import ../../cron_store/cron_recover_exact.bend as PX2
import ../../cron_store/cron_finish_exact.bend as PX3
import ../../cron_store/cron_cancel_exact.bend as PX4
import ../../cron_store/cron_resume_exact.bend as PX5

# Small parts
# -----------

def sx.in(+d: String, xs: List<&2, String>) -> {Sv.has_str(d, xs) == CronServe.sv_in(d, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %sx.in(d, t) : {Bool.or(String.eq(x, d), Sv.has_str(d, t)) == Bool.or(String.eq(x, d), _) : Bool}
      {==}

def sx.out_pick(b: Bool, x: String, r: List<&2, String>) -> {Sv.drop_str.put(b, x, r) == CronServe.sv_out.pick(b, x, r) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sx.out(+d: String, xs: List<&2, String>) -> {Sv.drop_str(d, xs) == CronServe.sv_out(d, xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %sx.out(d, t) : {Sv.drop_str.put(String.eq(x, d), x, Sv.drop_str(d, t)) == CronServe.sv_out.pick(String.eq(x, d), x, _) : List<&2, String>}
      sx.out_pick(String.eq(x, d), x, Sv.drop_str(d, t))

def sx.has(+n: Nat, xs: List<&2, Nat>) -> {Cr.has(n, xs) == CronServe.sv_has(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %sx.has(n, t) : {Bool.or(Nat.is_eq(x, n), Cr.has(n, t)) == Bool.or(Nat.is_eq(x, n), _) : Bool}
      {==}

def sx.same(js: List<&2, Sv.JRec>) -> {Sv.same(js) == CronServe.sv_same(js) : List<&2, Sv.JOut>}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      %sx.same(t) : {Sv.JSame{} <> Sv.same(t) == Sv.JSame{} <> _ : List<&2, Sv.JOut>}
      {==}

def sx.keep(cs: List<&2, Sv.CRec>) -> {Sv.keep(cs) == CronServe.sv_keep(cs) : List<&2, Sv.COut>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      %sx.keep(t) : {Sv.CKeep{} <> Sv.keep(t) == Sv.CKeep{} <> _ : List<&2, Sv.COut>}
      {==}

def sx.taken(cs: List<&2, Sv.CRec>) -> {Sv.claim_jobs(cs) == CronServe.sv_taken(cs) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case Sv.CKnown{d, +j, o}:
          %sx.taken(t) : {j <> Sv.claim_jobs(t) == j <> _ : List<&2, Nat>}
          {==}
        case Sv.CRaw{}:
          sx.taken(t)

def sx.moves(o: Sv.JOut) -> {Sv.jout_moves(o) == CronServe.sv_moves(o) : Bool}:
  match o:
    case Sv.JSame{}:
      {==}
    case Sv.JTook{t}:
      match t:
        case CS.Keep{}:
          {==}
        case CS.Roll{n}:
          {==}
        case CS.Claimed{n}:
          {==}
    case Sv.JBack{b}:
      match b:
        case CS.Kept{}:
          {==}
        case CS.Interrupted{st, n}:
          {==}
    case Sv.JFin{x}:
      match x:
        case CS.Untouched{}:
          {==}
        case CS.Ran{st, n, k}:
          {==}
        case CS.Skipped{st, n, k}:
          {==}
    case Sv.JCut{x}:
      match x:
        case CS.Same{}:
          {==}
        case CS.Cut{st, n}:
          {==}
    case Sv.JAgain{x}:
      match x:
        case CS.Resumed{st, n, k}:
          {==}
        case CS.Ended{}:
          {==}
        case CS.NotRecurring{}:
          {==}
    case Sv.JNew{}:
      {==}

def sx.jmoves(os: List<&2, Sv.JOut>) -> {Sv.jouts_move(os) == CronServe.sv_jmoves(os) : Bool}:
  match os:
    case Nil{}:
      {==}
    case +o <> +t:
      %sx.jmoves(t) : {Bool.or(Sv.jout_moves(o), Sv.jouts_move(t)) == Bool.or(CronServe.sv_moves(o), _) : Bool}
      %sx.moves(o) : {Bool.or(Sv.jout_moves(o), Sv.jouts_move(t)) == Bool.or(_, Sv.jouts_move(t)) : Bool}
      {==}

def sx.cmoves(os: List<&2, Sv.COut>) -> {Sv.couts_move(os) == CronServe.sv_cmoves(os) : Bool}:
  match os:
    case Nil{}:
      {==}
    case o <> +t:
      match o:
        case Sv.CKeep{}:
          sx.cmoves(t)
        case Sv.CDrop{}:
          {==}
        case Sv.CNew{k, d}:
          {==}

def sx.answer(aside: Bool, +jo: List<&2, Sv.JOut>, +co: List<&2, Sv.COut>) -> {Sv.out(aside, jo, co) == CronServe.sv_answer(aside, jo, co) : Sv.Out}:
  %sx.jmoves(jo) : {Sv.Out{aside, Bool.or(Sv.jouts_move(jo), Sv.couts_move(co)), jo, co} == Sv.Out{aside, Bool.or(_, CronServe.sv_cmoves(co)), jo, co} : Sv.Out}
  %sx.cmoves(co) : {Sv.Out{aside, Bool.or(Sv.jouts_move(jo), Sv.couts_move(co)), jo, co} == Sv.Out{aside, Bool.or(Sv.jouts_move(jo), _), jo, co} : Sv.Out}
  {==}

# The claim pass
# --------------

def sx.takes(t: CS.Took, fresh: List<&2, String>) -> {Sv.claim.takes(t, fresh) == CronServe.sv_claims(t, fresh) : Bool}:
  match t fresh:
    case CS.Keep{} _:
      {==}
    case CS.Roll{n} _:
      {==}
    case CS.Claimed{n} Nil{}:
      {==}
    case CS.Claimed{n} d <> r:
      {==}

def sx.took(t: CS.Took, fresh: List<&2, String>) -> {Sv.claim.out(t, fresh) == CronServe.sv_took(t, fresh) : Sv.JOut}:
  match t fresh:
    case CS.Keep{} _:
      {==}
    case CS.Roll{n} _:
      {==}
    case CS.Claimed{n} Nil{}:
      {==}
    case CS.Claimed{n} d <> r:
      {==}

def sx.set(b: Bool, +i: Nat, set: List<&2, Nat>) -> {Sv.claim.set(b, i, set) == CronServe.sv_taken_after(b, i, set) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sx.rest(b: Bool, fresh: List<&2, String>) -> {Sv.claim.rest(b, fresh) == CronServe.sv_fresh_after(b, fresh) : List<&2, String>}:
  match b fresh:
    case True{} Nil{}:
      {==}
    case True{} d <> r:
      {==}
    case False{} _:
      {==}

def sx.put(o: Sv.JOut, p: Sv.Pass) -> {Sv.claim.put(o, p) == CronServe.sv_pass_put(o, p) : Sv.Pass}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def sx.add(b: Bool, +k: Nat, fresh: List<&2, String>, o: Sv.JOut, p: Sv.Pass) -> {Sv.claim.add(b, k, fresh, o, p) == CronServe.sv_pass_add(b, k, fresh, o, p) : Sv.Pass}:
  match b fresh p:
    case True{} Nil{} Sv.Pass{jo, cn, ds}:
      {==}
    case True{} d <> r Sv.Pass{jo, cn, ds}:
      {==}
    case False{} _ Sv.Pass{jo, cn, ds}:
      {==}

def sx.new(+k: Nat, +d: String, o: Sv.JOut, p: Sv.Pass) -> {Sv.claim.new(k, d, o, p) == CronServe.sv_pass_new(k, d, o, p) : Sv.Pass}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

# one known job record, its claim pass decided (tk), the tail's pass the
# same on both sides (ih)
def sx.pass.at2(tk: CS.Took, +k: Nat, +i: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat, +t: List<&2, Sv.JRec>, ih: {Sv.claim(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now) == CronServe.sv_pass(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now) : Sv.Pass}) -> {Sv.claim.add(Sv.claim.takes(tk, fresh), k, fresh, Sv.claim.out(tk, fresh), Sv.claim(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now)) == CronServe.sv_pass_add(CronServe.sv_claims(tk, fresh), k, fresh, CronServe.sv_took(tk, fresh), CronServe.sv_pass(t, 1n+k, CronServe.sv_taken_after(CronServe.sv_claims(tk, fresh), i, set), CronServe.sv_fresh_after(CronServe.sv_claims(tk, fresh), fresh), due, now)) : Sv.Pass}:
  match tk fresh:
    case CS.Keep{} _:
      %ih : {Sv.claim.put(Sv.JTook{CS.Keep{}}, Sv.claim(t, 1n+k, set, fresh, due, now)) == CronServe.sv_pass_put(Sv.JTook{CS.Keep{}}, _) : Sv.Pass}
      sx.put(Sv.JTook{CS.Keep{}}, Sv.claim(t, 1n+k, set, fresh, due, now))
    case CS.Roll{+n} _:
      %ih : {Sv.claim.put(Sv.JTook{CS.Roll{n}}, Sv.claim(t, 1n+k, set, fresh, due, now)) == CronServe.sv_pass_put(Sv.JTook{CS.Roll{n}}, _) : Sv.Pass}
      sx.put(Sv.JTook{CS.Roll{n}}, Sv.claim(t, 1n+k, set, fresh, due, now))
    case CS.Claimed{+n} Nil{}:
      %ih : {Sv.claim.put(Sv.JSame{}, Sv.claim(t, 1n+k, set, Nil{}, due, now)) == CronServe.sv_pass_put(Sv.JSame{}, _) : Sv.Pass}
      sx.put(Sv.JSame{}, Sv.claim(t, 1n+k, set, Nil{}, due, now))
    case CS.Claimed{+n} +d <> +r:
      %ih : {Sv.claim.new(k, d, Sv.JTook{CS.Claimed{n}}, Sv.claim(t, 1n+k, i <> set, r, due, now)) == CronServe.sv_pass_new(k, d, Sv.JTook{CS.Claimed{n}}, _) : Sv.Pass}
      sx.new(k, d, Sv.JTook{CS.Claimed{n}}, Sv.claim(t, 1n+k, i <> set, r, due, now))

# the same, the spec's decision tk2 being the code's tk
def sx.pass.at(tk: CS.Took, tk2: CS.Took, eq: {tk == tk2 : CS.Took}, +k: Nat, +i: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat, +t: List<&2, Sv.JRec>, ih: {Sv.claim(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now) == CronServe.sv_pass(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now) : Sv.Pass}) -> {Sv.claim.add(Sv.claim.takes(tk, fresh), k, fresh, Sv.claim.out(tk, fresh), Sv.claim(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now)) == CronServe.sv_pass_add(CronServe.sv_claims(tk2, fresh), k, fresh, CronServe.sv_took(tk2, fresh), CronServe.sv_pass(t, 1n+k, CronServe.sv_taken_after(CronServe.sv_claims(tk2, fresh), i, set), CronServe.sv_fresh_after(CronServe.sv_claims(tk2, fresh), fresh), due, now)) : Sv.Pass}:
  %eq : {Sv.claim.add(Sv.claim.takes(tk, fresh), k, fresh, Sv.claim.out(tk, fresh), Sv.claim(t, 1n+k, Sv.claim.set(Sv.claim.takes(tk, fresh), i, set), Sv.claim.rest(Sv.claim.takes(tk, fresh), fresh), due, now)) == CronServe.sv_pass_add(CronServe.sv_claims(_, fresh), k, fresh, CronServe.sv_took(_, fresh), CronServe.sv_pass(t, 1n+k, CronServe.sv_taken_after(CronServe.sv_claims(_, fresh), i, set), CronServe.sv_fresh_after(CronServe.sv_claims(_, fresh), fresh), due, now)) : Sv.Pass}
  sx.pass.at2(tk, k, i, set, fresh, due, now, t, ih)

def sx.pass(js: List<&2, Sv.JRec>, +k: Nat, +set: List<&2, Nat>, +fresh: List<&2, String>, +due: Nat, +now: Nat) -> {Sv.claim(js, k, set, fresh, due, now) == CronServe.sv_pass(js, k, set, fresh, due, now) : Sv.Pass}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          %sx.pass(t, 1n+k, set, fresh, due, now) : {Sv.claim.put(Sv.JSame{}, Sv.claim(t, 1n+k, set, fresh, due, now)) == CronServe.sv_pass_put(Sv.JSame{}, _) : Sv.Pass}
          sx.put(Sv.JSame{}, Sv.claim(t, 1n+k, set, fresh, due, now))
        case Sv.JKnown{+i, +f}:
          +e = Equal.trans(CS.Took, CS.take(f, Cr.has(i, set), due, now), CS.take(f, CronServe.sv_has(i, set), due, now), CronStore.take_spec(f, CronServe.sv_has(i, set), due, now), Equal.cong(Bool, CS.Took, h => CS.take(f, h, due, now), Cr.has(i, set), CronServe.sv_has(i, set), sx.has(i, set)), CronStore.cron_take_exact(f, CronServe.sv_has(i, set), due, now))
          sx.pass.at(CS.take(f, Cr.has(i, set), due, now), CronStore.take_spec(f, CronServe.sv_has(i, set), due, now), e, k, i, set, fresh, due, now, t, sx.pass(t, 1n+k, Sv.claim.set(Sv.claim.takes(CS.take(f, Cr.has(i, set), due, now), fresh), i, set), Sv.claim.rest(Sv.claim.takes(CS.take(f, Cr.has(i, set), due, now), fresh), fresh), due, now))

def sx.claim_end(aside: Bool, +runs: List<&2, String>, +cs: List<&2, Sv.CRec>, p: Sv.Pass) -> {Sv.claim.end(aside, runs, cs, p) == CronServe.sv_claim_end(aside, runs, cs, p) : Sv.Served}:
  match p:
    case Sv.Pass{+jo, +cn, +ds}:
      %sx.keep(cs) : {Sv.Served{List.append(&2, String, ds, runs), Sv.out(aside, jo, List.append(&2, Sv.COut, Sv.keep(cs), cn))} == Sv.Served{List.append(&2, String, ds, runs), CronServe.sv_answer(aside, jo, List.append(&2, Sv.COut, _, cn))} : Sv.Served}
      Equal.cong(Sv.Out, Sv.Served, o => Sv.Served{List.append(&2, String, ds, runs), o}, Sv.out(aside, jo, List.append(&2, Sv.COut, Sv.keep(cs), cn)), CronServe.sv_answer(aside, jo, List.append(&2, Sv.COut, Sv.keep(cs), cn)), sx.answer(aside, jo, List.append(&2, Sv.COut, Sv.keep(cs), cn)))

# The recovery
# ------------

def sx.who(own: Bool, +d: String, +o: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>) -> {Sv.who(own, d, o, runs, dead) == CronServe.sv_who(own, d, o, runs, dead) : CS.Who}:
  match own:
    case True{}:
      Equal.cong(Bool, CS.Who, b => CS.Mine{b}, Sv.has_str(d, runs), CronServe.sv_in(d, runs), sx.in(d, runs))
    case False{}:
      Equal.cong(Bool, CS.Who, b => CS.Theirs{b}, Cr.has(o, dead), CronServe.sv_has(o, dead), sx.has(o, dead))

def sx.clears(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, c: Sv.CRec) -> {Sv.clears(me, runs, dead, c) == CronServe.sv_clears(me, runs, dead, c) : Bool}:
  match c:
    case Sv.CKnown{+d, j, +o}:
      %sx.who(Nat.is_eq(o, me), d, o, runs, dead) : {CS.clear(Sv.who(Nat.is_eq(o, me), d, o, runs, dead)) == CronStore.clear_spec(_) : Bool}
      CronStore.cron_clear_exact(Sv.who(Nat.is_eq(o, me), d, o, runs, dead))
    case Sv.CRaw{}:
      {==}

def sx.cleared_pick(b: Bool, +j: Nat, r: List<&2, Nat>) -> {Sv.cleared.pick(b, j, r) == CronServe.sv_cleared.pick(b, j, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sx.cleared(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, Sv.CRec>) -> {Sv.cleared(me, runs, dead, cs) == CronServe.sv_cleared(me, runs, dead, cs) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case Sv.CKnown{+d, +j, +o}:
          %sx.cleared(me, runs, dead, t) : {Sv.cleared.pick(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o}), j, Sv.cleared(me, runs, dead, t)) == CronServe.sv_cleared.pick(CronServe.sv_clears(me, runs, dead, Sv.CKnown{d, j, o}), j, _) : List<&2, Nat>}
          %sx.clears(me, runs, dead, Sv.CKnown{d, j, o}) : {Sv.cleared.pick(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o}), j, Sv.cleared(me, runs, dead, t)) == CronServe.sv_cleared.pick(_, j, Sv.cleared(me, runs, dead, t)) : List<&2, Nat>}
          sx.cleared_pick(Sv.clears(me, runs, dead, Sv.CKnown{d, j, o}), j, Sv.cleared(me, runs, dead, t))
        case Sv.CRaw{}:
          sx.cleared(me, runs, dead, t)

def sx.drop_if(b: Bool) -> {Sv.recover.claim(b) == CronServe.sv_drop_if(b) : Sv.COut}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sx.recover_claims(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, cs: List<&2, Sv.CRec>) -> {Sv.recover.claims(me, runs, dead, cs) == CronServe.sv_recover_claims(me, runs, dead, cs) : List<&2, Sv.COut>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %sx.recover_claims(me, runs, dead, t) : {Sv.recover.claim(Sv.clears(me, runs, dead, c)) <> Sv.recover.claims(me, runs, dead, t) == CronServe.sv_drop_if(CronServe.sv_clears(me, runs, dead, c)) <> _ : List<&2, Sv.COut>}
      %sx.clears(me, runs, dead, c) : {Sv.recover.claim(Sv.clears(me, runs, dead, c)) <> Sv.recover.claims(me, runs, dead, t) == CronServe.sv_drop_if(_) <> Sv.recover.claims(me, runs, dead, t) : List<&2, Sv.COut>}
      %sx.drop_if(Sv.clears(me, runs, dead, c)) : {Sv.recover.claim(Sv.clears(me, runs, dead, c)) <> Sv.recover.claims(me, runs, dead, t) == _ <> Sv.recover.claims(me, runs, dead, t) : List<&2, Sv.COut>}
      {==}

def sx.recover_jobs(+ids: List<&2, Nat>, js: List<&2, Sv.JRec>) -> {Sv.recover.jobs(ids, js) == CronServe.sv_recover_jobs(ids, js) : List<&2, Sv.JOut>}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          %sx.recover_jobs(ids, t) : {Sv.JSame{} <> Sv.recover.jobs(ids, t) == Sv.JSame{} <> _ : List<&2, Sv.JOut>}
          {==}
        case Sv.JKnown{+i, +f}:
          %sx.recover_jobs(ids, t) : {Sv.JBack{CS.recover(f, Cr.has(i, ids))} <> Sv.recover.jobs(ids, t) == Sv.JBack{CronStore.recover_spec(f, CronServe.sv_has(i, ids))} <> _ : List<&2, Sv.JOut>}
          %sx.has(i, ids) : {Sv.JBack{CS.recover(f, Cr.has(i, ids))} <> Sv.recover.jobs(ids, t) == Sv.JBack{CronStore.recover_spec(f, _)} <> Sv.recover.jobs(ids, t) : List<&2, Sv.JOut>}
          %CronStore.cron_recover_exact(f, Cr.has(i, ids)) : {Sv.JBack{CS.recover(f, Cr.has(i, ids))} <> Sv.recover.jobs(ids, t) == Sv.JBack{_} <> Sv.recover.jobs(ids, t) : List<&2, Sv.JOut>}
          {==}

# The finish step
# ---------------

def sx.claim_of_pick(b: Bool, j: Nat, o: Nat, r: Maybe<&2, Sv.Hit>) -> {Sv.claim_of.pick(b, j, o, r) == CronServe.sv_claim_of.pick(b, j, o, r) : Maybe<&2, Sv.Hit>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sx.claim_of(+d: String, cs: List<&2, Sv.CRec>) -> {Sv.claim_of(d, cs) == CronServe.sv_claim_of(d, cs) : Maybe<&2, Sv.Hit>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case Sv.CKnown{+x, +j, +o}:
          %sx.claim_of(d, t) : {Sv.claim_of.pick(String.eq(x, d), j, o, Sv.claim_of(d, t)) == CronServe.sv_claim_of.pick(String.eq(x, d), j, o, _) : Maybe<&2, Sv.Hit>}
          sx.claim_of_pick(String.eq(x, d), j, o, Sv.claim_of(d, t))
        case Sv.CRaw{}:
          sx.claim_of(d, t)

def sx.drop_first_pick(b: Bool, +t: List<&2, Sv.CRec>, r: List<&2, Sv.COut>) -> {Sv.drop_first.pick(b, t, r) == CronServe.sv_drop_first.pick(b, t, r) : List<&2, Sv.COut>}:
  match b:
    case True{}:
      %sx.keep(t) : {Sv.CDrop{} <> Sv.keep(t) == Sv.CDrop{} <> _ : List<&2, Sv.COut>}
      {==}
    case False{}:
      {==}

def sx.drop_first(+d: String, cs: List<&2, Sv.CRec>) -> {Sv.drop_first(d, cs) == CronServe.sv_drop_first(d, cs) : List<&2, Sv.COut>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case Sv.CKnown{+x, j, o}:
          %sx.drop_first(d, t) : {Sv.drop_first.pick(String.eq(x, d), t, Sv.drop_first(d, t)) == CronServe.sv_drop_first.pick(String.eq(x, d), t, _) : List<&2, Sv.COut>}
          sx.drop_first_pick(String.eq(x, d), t, Sv.drop_first(d, t))
        case Sv.CRaw{}:
          %sx.drop_first(d, t) : {Sv.CKeep{} <> Sv.drop_first(d, t) == Sv.CKeep{} <> _ : List<&2, Sv.COut>}
          {==}

def sx.if(b: Bool, a: Sv.JOut) -> {Sv.finish.pick(b, a) == CronServe.sv_if(b, a) : Sv.JOut}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sx.finish_jobs(+j: Nat, +ran: Bool, +failed: Bool, +now: Nat, js: List<&2, Sv.JRec>) -> {Sv.finish.jobs(j, ran, failed, now, js) == CronServe.sv_finish_jobs(j, ran, failed, now, js) : List<&2, Sv.JOut>}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          %sx.finish_jobs(j, ran, failed, now, t) : {Sv.JSame{} <> Sv.finish.jobs(j, ran, failed, now, t) == Sv.JSame{} <> _ : List<&2, Sv.JOut>}
          {==}
        case Sv.JKnown{+i, +f}:
          %sx.finish_jobs(j, ran, failed, now, t) : {Sv.finish.pick(Nat.is_eq(i, j), Sv.JFin{CS.finish(60000n, f, ran, failed, now)}) <> Sv.finish.jobs(j, ran, failed, now, t) == CronServe.sv_if(Nat.is_eq(i, j), Sv.JFin{CronStore.finish_spec(60000n, f, ran, failed, now)}) <> _ : List<&2, Sv.JOut>}
          %CronStore.cron_finish_exact(60000n, f, ran, failed, now) : {Sv.finish.pick(Nat.is_eq(i, j), Sv.JFin{CS.finish(60000n, f, ran, failed, now)}) <> Sv.finish.jobs(j, ran, failed, now, t) == CronServe.sv_if(Nat.is_eq(i, j), Sv.JFin{_}) <> Sv.finish.jobs(j, ran, failed, now, t) : List<&2, Sv.JOut>}
          %sx.if(Nat.is_eq(i, j), Sv.JFin{CS.finish(60000n, f, ran, failed, now)}) : {Sv.finish.pick(Nat.is_eq(i, j), Sv.JFin{CS.finish(60000n, f, ran, failed, now)}) <> Sv.finish.jobs(j, ran, failed, now, t) == _ <> Sv.finish.jobs(j, ran, failed, now, t) : List<&2, Sv.JOut>}
          {==}

def sx.unchanged(aside: Bool, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {Sv.Out{aside, False{}, Sv.same(js), Sv.keep(cs)} == Sv.Out{aside, False{}, CronServe.sv_same(js), CronServe.sv_keep(cs)} : Sv.Out}:
  %sx.same(js) : {Sv.Out{aside, False{}, Sv.same(js), Sv.keep(cs)} == Sv.Out{aside, False{}, _, CronServe.sv_keep(cs)} : Sv.Out}
  %sx.keep(cs) : {Sv.Out{aside, False{}, Sv.same(js), Sv.keep(cs)} == Sv.Out{aside, False{}, Sv.same(js), _} : Sv.Out}
  {==}

def sx.finish_own(own: Bool, aside: Bool, +j: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {Sv.finish.own(own, aside, j, d, ran, failed, now, js, cs) == CronServe.sv_finish_own(own, aside, j, d, ran, failed, now, js, cs) : Sv.Out}:
  match own:
    case True{}:
      %sx.finish_jobs(j, ran, failed, now, js) : {Sv.out(aside, Sv.finish.jobs(j, ran, failed, now, js), Sv.drop_first(d, cs)) == CronServe.sv_answer(aside, _, CronServe.sv_drop_first(d, cs)) : Sv.Out}
      %sx.drop_first(d, cs) : {Sv.out(aside, Sv.finish.jobs(j, ran, failed, now, js), Sv.drop_first(d, cs)) == CronServe.sv_answer(aside, Sv.finish.jobs(j, ran, failed, now, js), _) : Sv.Out}
      sx.answer(aside, Sv.finish.jobs(j, ran, failed, now, js), Sv.drop_first(d, cs))
    case False{}:
      sx.unchanged(aside, js, cs)

def sx.finish_found(m: Maybe<&2, Sv.Hit>, +me: Nat, aside: Bool, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {Sv.finish.found(m, me, aside, d, ran, failed, now, js, cs) == CronServe.sv_finish_found(m, me, aside, d, ran, failed, now, js, cs) : Sv.Out}:
  match m:
    case None{}:
      sx.unchanged(aside, js, cs)
    case Some{p}:
      match p:
        case Sv.Hit{+j, +o}:
          sx.finish_own(Nat.is_eq(o, me), aside, j, d, ran, failed, now, js, cs)

def sx.finish(run: Bool, +me: Nat, +runs: List<&2, String>, aside: Bool, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {Sv.finish(run, me, runs, aside, d, ran, failed, now, js, cs) == CronServe.sv_finish(run, me, runs, aside, d, ran, failed, now, js, cs) : Sv.Served}:
  match run:
    case True{}:
      %sx.out(d, runs) : {Sv.Served{Sv.drop_str(d, runs), Sv.finish.found(Sv.claim_of(d, cs), me, aside, d, ran, failed, now, js, cs)} == Sv.Served{_, CronServe.sv_finish_found(CronServe.sv_claim_of(d, cs), me, aside, d, ran, failed, now, js, cs)} : Sv.Served}
      %sx.claim_of(d, cs) : {Sv.Served{Sv.drop_str(d, runs), Sv.finish.found(Sv.claim_of(d, cs), me, aside, d, ran, failed, now, js, cs)} == Sv.Served{Sv.drop_str(d, runs), CronServe.sv_finish_found(_, me, aside, d, ran, failed, now, js, cs)} : Sv.Served}
      Equal.cong(Sv.Out, Sv.Served, o => Sv.Served{Sv.drop_str(d, runs), o}, Sv.finish.found(Sv.claim_of(d, cs), me, aside, d, ran, failed, now, js, cs), CronServe.sv_finish_found(Sv.claim_of(d, cs), me, aside, d, ran, failed, now, js, cs), sx.finish_found(Sv.claim_of(d, cs), me, aside, d, ran, failed, now, js, cs))
    case False{}:
      Equal.cong(Sv.Out, Sv.Served, o => Sv.Served{runs, o}, Sv.Out{aside, False{}, Sv.same(js), Sv.keep(cs)}, Sv.Out{aside, False{}, CronServe.sv_same(js), CronServe.sv_keep(cs)}, sx.unchanged(aside, js, cs))

# User actions
# ------------

def sx.cancel_jobs(+n: Nat, js: List<&2, Sv.JRec>) -> {Sv.cancel.jobs(n, js) == CronServe.sv_cancel_jobs(n, js) : List<&2, Sv.JOut>}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          %sx.cancel_jobs(n, t) : {Sv.JSame{} <> Sv.cancel.jobs(n, t) == Sv.JSame{} <> _ : List<&2, Sv.JOut>}
          {==}
        case Sv.JKnown{+i, +f}:
          %sx.cancel_jobs(n, t) : {Sv.finish.pick(Nat.is_eq(i, n), Sv.JCut{CS.cancel(f)}) <> Sv.cancel.jobs(n, t) == CronServe.sv_if(Nat.is_eq(i, n), Sv.JCut{CronStore.cancel_spec(f)}) <> _ : List<&2, Sv.JOut>}
          %CronStore.cron_cancel_exact(f) : {Sv.finish.pick(Nat.is_eq(i, n), Sv.JCut{CS.cancel(f)}) <> Sv.cancel.jobs(n, t) == CronServe.sv_if(Nat.is_eq(i, n), Sv.JCut{_}) <> Sv.cancel.jobs(n, t) : List<&2, Sv.JOut>}
          %sx.if(Nat.is_eq(i, n), Sv.JCut{CS.cancel(f)}) : {Sv.finish.pick(Nat.is_eq(i, n), Sv.JCut{CS.cancel(f)}) <> Sv.cancel.jobs(n, t) == _ <> Sv.cancel.jobs(n, t) : List<&2, Sv.JOut>}
          {==}

def sx.resume_jobs(+n: Nat, +now: Nat, js: List<&2, Sv.JRec>) -> {Sv.resume.jobs(n, now, js) == CronServe.sv_resume_jobs(n, now, js) : List<&2, Sv.JOut>}:
  match js:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Sv.JRaw{}:
          %sx.resume_jobs(n, now, t) : {Sv.JSame{} <> Sv.resume.jobs(n, now, t) == Sv.JSame{} <> _ : List<&2, Sv.JOut>}
          {==}
        case Sv.JKnown{+i, +f}:
          %sx.resume_jobs(n, now, t) : {Sv.finish.pick(Nat.is_eq(i, n), Sv.JAgain{CS.resume(f, now)}) <> Sv.resume.jobs(n, now, t) == CronServe.sv_if(Nat.is_eq(i, n), Sv.JAgain{CronStore.resume_spec(f, now)}) <> _ : List<&2, Sv.JOut>}
          %CronStore.cron_resume_exact(f, now) : {Sv.finish.pick(Nat.is_eq(i, n), Sv.JAgain{CS.resume(f, now)}) <> Sv.resume.jobs(n, now, t) == CronServe.sv_if(Nat.is_eq(i, n), Sv.JAgain{_}) <> Sv.resume.jobs(n, now, t) : List<&2, Sv.JOut>}
          %sx.if(Nat.is_eq(i, n), Sv.JAgain{CS.resume(f, now)}) : {Sv.finish.pick(Nat.is_eq(i, n), Sv.JAgain{CS.resume(f, now)}) <> Sv.resume.jobs(n, now, t) == _ <> Sv.resume.jobs(n, now, t) : List<&2, Sv.JOut>}
          {==}

# One update
# ----------

def sx.served(+runs: List<&2, String>, aside: Bool, +jo: List<&2, Sv.JOut>, +co: List<&2, Sv.COut>) -> {Sv.Served{runs, Sv.out(aside, jo, co)} == Sv.Served{runs, CronServe.sv_answer(aside, jo, co)} : Sv.Served}:
  Equal.cong(Sv.Out, Sv.Served, o => Sv.Served{runs, o}, Sv.out(aside, jo, co), CronServe.sv_answer(aside, jo, co), sx.answer(aside, jo, co))

def sx.go(+runs: List<&2, String>, +me: Nat, aside: Bool, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, op: Sv.Op) -> {Sv.go(runs, me, aside, js, cs, op) == CronServe.sv_go(runs, me, aside, js, cs, op) : Sv.Served}:
  match op:
    case Sv.OClaim{+due, +now, +fresh}:
      %sx.taken(cs) : {Sv.claim.end(aside, runs, cs, Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now)) == CronServe.sv_claim_end(aside, runs, cs, CronServe.sv_pass(js, 0n, _, fresh, due, now)) : Sv.Served}
      %sx.pass(js, 0n, Sv.claim_jobs(cs), fresh, due, now) : {Sv.claim.end(aside, runs, cs, Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now)) == CronServe.sv_claim_end(aside, runs, cs, _) : Sv.Served}
      sx.claim_end(aside, runs, cs, Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now))
    case Sv.ORecover{+dead}:
      %sx.cleared(me, runs, dead, cs) : {Sv.Served{runs, Sv.out(aside, Sv.recover.jobs(Sv.cleared(me, runs, dead, cs), js), Sv.recover.claims(me, runs, dead, cs))} == Sv.Served{runs, CronServe.sv_answer(aside, CronServe.sv_recover_jobs(_, js), CronServe.sv_recover_claims(me, runs, dead, cs))} : Sv.Served}
      %sx.recover_jobs(Sv.cleared(me, runs, dead, cs), js) : {Sv.Served{runs, Sv.out(aside, Sv.recover.jobs(Sv.cleared(me, runs, dead, cs), js), Sv.recover.claims(me, runs, dead, cs))} == Sv.Served{runs, CronServe.sv_answer(aside, _, CronServe.sv_recover_claims(me, runs, dead, cs))} : Sv.Served}
      %sx.recover_claims(me, runs, dead, cs) : {Sv.Served{runs, Sv.out(aside, Sv.recover.jobs(Sv.cleared(me, runs, dead, cs), js), Sv.recover.claims(me, runs, dead, cs))} == Sv.Served{runs, CronServe.sv_answer(aside, Sv.recover.jobs(Sv.cleared(me, runs, dead, cs), js), _)} : Sv.Served}
      sx.served(runs, aside, Sv.recover.jobs(Sv.cleared(me, runs, dead, cs), js), Sv.recover.claims(me, runs, dead, cs))
    case Sv.OFinish{+d, +ran, +failed, +now}:
      %sx.in(d, runs) : {Sv.finish(Sv.has_str(d, runs), me, runs, aside, d, ran, failed, now, js, cs) == CronServe.sv_finish(_, me, runs, aside, d, ran, failed, now, js, cs) : Sv.Served}
      sx.finish(Sv.has_str(d, runs), me, runs, aside, d, ran, failed, now, js, cs)
    case Sv.OCancel{+n}:
      %sx.cancel_jobs(n, js) : {Sv.Served{runs, Sv.out(aside, Sv.cancel.jobs(n, js), Sv.keep(cs))} == Sv.Served{runs, CronServe.sv_answer(aside, _, CronServe.sv_keep(cs))} : Sv.Served}
      %sx.keep(cs) : {Sv.Served{runs, Sv.out(aside, Sv.cancel.jobs(n, js), Sv.keep(cs))} == Sv.Served{runs, CronServe.sv_answer(aside, Sv.cancel.jobs(n, js), _)} : Sv.Served}
      sx.served(runs, aside, Sv.cancel.jobs(n, js), Sv.keep(cs))
    case Sv.OResume{+n, +now}:
      %sx.resume_jobs(n, now, js) : {Sv.Served{runs, Sv.out(aside, Sv.resume.jobs(n, now, js), Sv.keep(cs))} == Sv.Served{runs, CronServe.sv_answer(aside, _, CronServe.sv_keep(cs))} : Sv.Served}
      %sx.keep(cs) : {Sv.Served{runs, Sv.out(aside, Sv.resume.jobs(n, now, js), Sv.keep(cs))} == Sv.Served{runs, CronServe.sv_answer(aside, Sv.resume.jobs(n, now, js), _)} : Sv.Served}
      sx.served(runs, aside, Sv.resume.jobs(n, now, js), Sv.keep(cs))
    case Sv.OCreate{n, f}:
      %sx.same(js) : {Sv.Served{runs, Sv.out(aside, List.append(&2, Sv.JOut, Sv.same(js), [Sv.JNew{}]), Sv.keep(cs))} == Sv.Served{runs, CronServe.sv_answer(aside, List.append(&2, Sv.JOut, _, [Sv.JNew{}]), CronServe.sv_keep(cs))} : Sv.Served}
      %sx.keep(cs) : {Sv.Served{runs, Sv.out(aside, List.append(&2, Sv.JOut, Sv.same(js), [Sv.JNew{}]), Sv.keep(cs))} == Sv.Served{runs, CronServe.sv_answer(aside, List.append(&2, Sv.JOut, Sv.same(js), [Sv.JNew{}]), _)} : Sv.Served}
      sx.served(runs, aside, List.append(&2, Sv.JOut, Sv.same(js), [Sv.JNew{}]), Sv.keep(cs))

# the serve the stepper runs is the spec's
def sx.serve(+runs: List<&2, String>, +me: Nat, disk: Sv.Disk, op: Sv.Op) -> {Sv.serve(runs, me, disk, op) == CronServe.sv_serve(runs, me, disk, op) : Sv.Served}:
  match disk:
    case Sv.Missing{}:
      sx.go(runs, me, False{}, Nil{}, Nil{}, op)
    case Sv.Torn{}:
      sx.go(runs, me, True{}, Nil{}, Nil{}, op)
    case Sv.Parsed{js, cs}:
      sx.go(runs, me, False{}, js, cs, op)
