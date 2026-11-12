# eukhe: the proof of LAW rows_are_entries
#
# PROOF: rows.go makes, for the entry at place k, at most one row: at
# place k, with the scan's verdict on the entry (the same verdict: the one
# the scan answers at that place) and the newest of its times (lra.head,
# lra.newest_ok); the rows of the later entries stand for their entries,
# one place on (lra.lift). Insertion sort keeps every row (lra.ins,
# lra.sort), so every row of the listing stands for its entry.

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg
import ./base/order.bend as LO
import ./base/scan.bend as LA
import ./base/rows.bend as LR
import ./rows_are_entries/newest.bend as LN

# the row x stands for the entry at its place in os (the first at place
# k), ps the scan's verdicts at the same places
def lra.q(x: Ls.Row, os: List<&2, Ls.Obs>, ps: List<&2, Ls.Pick>, +k: Nat) -> Bool:
  match x:
    case Ls.Row{i, p, t}:
      Listing.sp_row_at_ok(os, ps, k, i, p, t)

def lra.all(rs: List<&2, Ls.Row>, +os: List<&2, Ls.Obs>, +ps: List<&2, Ls.Pick>, +k: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(lra.q(r, os, ps, k), lra.all(rest, os, ps, k))

def lra.mq(m: Maybe<&2, Ls.Row>, os: List<&2, Ls.Obs>, ps: List<&2, Ls.Pick>, +k: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{r}:
      lra.q(r, os, ps, k)

# a row of the entries after o stands for its entry among o and them too
def lra.q_lift(x: Ls.Row, +o: Ls.Obs, -rest: List<&2, Ls.Obs>, +q: Ls.Pick, -qs: List<&2, Ls.Pick>, +k: Nat, h: {lra.q(x, rest, qs, 1n+k) == True{} : Bool}) -> {lra.q(x, o <> rest, q <> qs, k) == True{} : Bool}:
  match x:
    case Ls.Row{+i, +p, +t}:
      %Equal.sym(Bool, Listing.sp_row_at_ok(rest, qs, 1n+k, i, p, t), True{}, h) : {Bool.or(Bool.and(Nat.is_eq(k, i), Bool.and(Listing.sp_pick_same(p, q), Listing.sp_newest_ok(t, Listing.sp_obs_times(o)))), _) == True{} : Bool}
      LA.ls.or_true(Bool.and(Nat.is_eq(k, i), Bool.and(Listing.sp_pick_same(p, q), Listing.sp_newest_ok(t, Listing.sp_obs_times(o)))))

def lra.lift(rs: List<&2, Ls.Row>, +o: Ls.Obs, +rest: List<&2, Ls.Obs>, +q: Ls.Pick, +qs: List<&2, Ls.Pick>, +k: Nat, +h: {lra.all(rs, rest, qs, 1n+k) == True{} : Bool}) -> {lra.all(rs, o <> rest, q <> qs, k) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +x <> +r:
      +hx = LR.lr.and_l(lra.q(x, rest, qs, 1n+k), lra.all(r, rest, qs, 1n+k), h)
      +hr = LR.lr.and_r(lra.q(x, rest, qs, 1n+k), lra.all(r, rest, qs, 1n+k), h)
      LR.lr.and_tt(lra.q(x, o <> rest, q <> qs, k), lra.all(r, o <> rest, q <> qs, k), lra.q_lift(x, o, rest, q, qs, k, hx), lra.lift(r, o, rest, q, qs, k, hr))

def lra.put(m: Maybe<&2, Ls.Row>, R: List<&2, Ls.Row>, +os: List<&2, Ls.Obs>, +ps: List<&2, Ls.Pick>, +k: Nat, hm: {lra.mq(m, os, ps, k) == True{} : Bool}, hR: {lra.all(R, os, ps, k) == True{} : Bool}) -> {lra.all(Ls.row.put(m, R), os, ps, k) == True{} : Bool}:
  match m:
    case None{}:
      hR
    case Some{+x}:
      LR.lr.and_tt(lra.q(x, os, ps, k), lra.all(R, os, ps, k), hm, hR)

# the row of a kept verdict at place k, with the newest time
def lra.at(+s: String, +P: Ls.Pick, -e: Sg.Seen, -c: Maybe<&2, String>, +t0: Sg.Time, +rt: List<&2, Sg.Time>, -rest: List<&2, Ls.Obs>, -qs: List<&2, Ls.Pick>, +k: Nat, hp: {Listing.sp_pick_same(P, P) == True{} : Bool}) -> {lra.q(Ls.Row{k, P, Ls.newest(rt, t0)}, Ls.Obs{e, c, t0 <> rt} <> rest, P <> qs, k) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(k, k), True{}, LR.lr.eq_refl(k)) : {Bool.or(Bool.and(_, Bool.and(Listing.sp_pick_same(P, P), Listing.sp_newest_ok(Ls.newest(rt, t0), t0 <> rt))), Listing.sp_row_at_ok(rest, qs, 1n+k, k, P, Ls.newest(rt, t0))) == True{} : Bool}
  %Equal.sym(Bool, Listing.sp_pick_same(P, P), True{}, hp) : {Bool.or(Bool.and(True{}, Bool.and(_, Listing.sp_newest_ok(Ls.newest(rt, t0), t0 <> rt))), Listing.sp_row_at_ok(rest, qs, 1n+k, k, P, Ls.newest(rt, t0))) == True{} : Bool}
  %Equal.sym(Bool, Listing.sp_newest_ok(Ls.newest(rt, t0), t0 <> rt), True{}, LN.lra.newest_ok(rt, t0)) : {Bool.or(Bool.and(True{}, Bool.and(True{}, _)), Listing.sp_row_at_ok(rest, qs, 1n+k, k, P, Ls.newest(rt, t0))) == True{} : Bool}
  {==}

def lra.times(+P: Ls.Pick, -e: Sg.Seen, -c: Maybe<&2, String>, ts: List<&2, Sg.Time>, -rest: List<&2, Ls.Obs>, -qs: List<&2, Ls.Pick>, +k: Nat, +s: String, hp: {Listing.sp_pick_same(P, P) == True{} : Bool}) -> {lra.mq(Ls.row.times(P, k, ts), Ls.Obs{e, c, ts} <> rest, P <> qs, k) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t0 <> +rt:
      lra.at(s, P, e, c, t0, rt, rest, qs, k, hp)

def lra.cwd(ok: Bool, +P: Ls.Pick, -e: Sg.Seen, -c: Maybe<&2, String>, ts: List<&2, Sg.Time>, -rest: List<&2, Ls.Obs>, -qs: List<&2, Ls.Pick>, +k: Nat, +s: String, hp: {Listing.sp_pick_same(P, P) == True{} : Bool}) -> {lra.mq(Ls.row.cwd(ok, P, k, ts), Ls.Obs{e, c, ts} <> rest, P <> qs, k) == True{} : Bool}:
  match ok:
    case True{}:
      lra.times(P, e, c, ts, rest, qs, k, s, hp)
    case False{}:
      {==}

# the row of the entry at place k stands for it
def lra.head(P: Ls.Pick, ok: Bool, -e: Sg.Seen, -c: Maybe<&2, String>, ts: List<&2, Sg.Time>, -rest: List<&2, Ls.Obs>, -qs: List<&2, Ls.Pick>, +k: Nat) -> {lra.mq(Ls.row.pick(P, k, ok, ts), Ls.Obs{e, c, ts} <> rest, P <> qs, k) == True{} : Bool}:
  match P:
    case Ls.PSkip{}:
      {==}
    case Ls.PStore{+s}:
      lra.cwd(ok, Ls.PStore{s}, e, c, ts, rest, qs, k, s, LStg.stg.same_refl(s))
    case Ls.PLegacy{+s}:
      lra.cwd(ok, Ls.PLegacy{s}, e, c, ts, rest, qs, k, s, LStg.stg.same_refl(s))

# every row of rows.go stands for its entry
def lra.go(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>, +k: Nat) -> {lra.all(Ls.rows.go(os, all, k), os, Ls.scan.go(Ls.seens(os), all), k) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Ls.Obs{+e, +c, +ts}:
          +o2 = {Ls.Obs{e, c, ts} : Ls.Obs}
          +P = Ls.pick(e, all)
          +qs = Ls.scan.go(Ls.seens(rest), all)
          lra.put(Ls.row(o2, all, k), Ls.rows.go(rest, all, 1n+k), o2 <> rest, P <> qs, k, lra.head(P, Ls.cwd_ok(c), e, c, ts, rest, qs, k), lra.lift(Ls.rows.go(rest, all, 1n+k), o2, rest, P, qs, k, lra.go(rest, all, 1n+k)))

def lra.ins(ys: List<&2, Ls.Row>, +x: Ls.Row, h: Bool, +os: List<&2, Ls.Obs>, +ps: List<&2, Ls.Pick>, +k: Nat) -> {lra.all(Ls.ins(ys, x, h), os, ps, k) == Bool.and(lra.q(x, os, ps, k), lra.all(ys, os, ps, k)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      match h:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Bool, lra.all(Ls.ins(rest, x, Ls.ins.head(x, rest)), os, ps, k), Bool.and(lra.q(x, os, ps, k), lra.all(rest, os, ps, k)), lra.ins(rest, x, Ls.ins.head(x, rest), os, ps, k)) : {Bool.and(lra.q(y, os, ps, k), _) == Bool.and(lra.q(x, os, ps, k), Bool.and(lra.q(y, os, ps, k), lra.all(rest, os, ps, k))) : Bool}
          LR.lr.and_swap(lra.q(y, os, ps, k), lra.q(x, os, ps, k), lra.all(rest, os, ps, k))

def lra.sort(xs: List<&2, Ls.Row>, +os: List<&2, Ls.Obs>, +ps: List<&2, Ls.Pick>, +k: Nat) -> {lra.all(Ls.sort(xs), os, ps, k) == lra.all(xs, os, ps, k) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, lra.all(Ls.ins(Ls.sort(rest), x, Ls.ins.head(x, Ls.sort(rest))), os, ps, k), Bool.and(lra.q(x, os, ps, k), lra.all(Ls.sort(rest), os, ps, k)), lra.ins(Ls.sort(rest), x, Ls.ins.head(x, Ls.sort(rest)), os, ps, k)) : {_ == Bool.and(lra.q(x, os, ps, k), lra.all(rest, os, ps, k)) : Bool}
      %Equal.sym(Bool, lra.all(Ls.sort(rest), os, ps, k), lra.all(rest, os, ps, k), lra.sort(rest, os, ps, k)) : {Bool.and(lra.q(x, os, ps, k), _) == Bool.and(lra.q(x, os, ps, k), lra.all(rest, os, ps, k)) : Bool}
      {==}

def lra.ok(rs: List<&2, Ls.Row>, +ps: List<&2, Ls.Pick>, +os: List<&2, Ls.Obs>) -> {Listing.sp_rows_ok(rs, ps, os) == lra.all(rs, os, ps, 0n) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Ls.Row{+i, +p, +t}:
          %lra.ok(rest, ps, os) : {Bool.and(Listing.sp_row_at_ok(os, ps, 0n, i, p, t), Listing.sp_rows_ok(rest, ps, os)) == Bool.and(Listing.sp_row_at_ok(os, ps, 0n, i, p, t), _) : Bool}
          {==}

def Listing.rows_are_entries(os):
  +A = Ls.seens(os)
  +ps = Ls.scan(A)
  %LR.lr.seens(os) : {Listing.sp_rows_ok(Ls.rows(os), Ls.scan(_), os) == True{} : Bool}
  %Equal.sym(Bool, Listing.sp_rows_ok(Ls.rows(os), ps, os), lra.all(Ls.rows(os), os, ps, 0n), lra.ok(Ls.rows(os), ps, os)) : {_ == True{} : Bool}
  %Equal.sym(Bool, lra.all(Ls.sort(Ls.rows.go(os, A, 0n)), os, ps, 0n), lra.all(Ls.rows.go(os, A, 0n), os, ps, 0n), lra.sort(Ls.rows.go(os, A, 0n), os, ps, 0n)) : {_ == True{} : Bool}
  lra.go(os, A, 0n)
