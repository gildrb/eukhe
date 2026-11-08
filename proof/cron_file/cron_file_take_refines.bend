# eukhe: the proof of LAW cron_file_take_refines
# Job by job (the first job of id x, proof/cron_file/base/file.bend): the
# claim pass of that job sees a claim record exactly when the job has a
# claim on record (no two jobs share an id), so its answer is the one
# cron_take_refines ties to the model's claim step; its row is that
# answer, and the claim records naming x are its claim on record plus the
# one record the pass adds when it claims the job. Every other job's
# records name other ids; the records this build cannot read stay.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ../cron/cron_take_refines.bend as PTakeRefines
import ./base/file.bend as LCfd
import ./base/logic.bend as LCfl

# Claimed
# -------

def cft.mclaimed(m: Maybe<&2, Cr.Job>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{j}:
      Cron.claimed_of(j)

def cft.keys_none_one(+i: Nat, cl: Maybe<&2, Cr.Claim>, +x: Nat, +rest: List<&2, Maybe<&2, Nat>>, ne: {Nat.is_eq(x, i) == False{} : Bool}, ih: {CronFile.claimed_spec(x, rest) == False{} : Bool}) -> {CronFile.claimed_spec(x, CronFileView.keys_one(i, cl, rest)) == False{} : Bool}:
  match cl:
    case None{}:
      ih
    case Some{c}:
      %Equal.sym(Bool, Nat.is_eq(x, i), False{}, ne) : {Bool.or(_, CronFile.claimed_spec(x, rest)) == False{} : Bool}
      ih

def cft.keys_none(+x: Nat, rs: List<&2, Cr.Rec>, +h: {CronFileView.has_id(x, rs) == False{} : Bool}) -> {CronFile.claimed_spec(x, CronFileView.keys_of(rs)) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +hh}:
              +ne = LCfl.cfl.ne_comm(i, x, LCfd.cfd.has_head(Cr.Job{i, s, st, nx, k, cl, ru, ss, hh}, t, x, h))
              cft.keys_none_one(i, cl, x, CronFileView.keys_of(t), ne, cft.keys_none(x, t, LCfd.cfd.has_tail(Cr.Job{i, s, st, nx, k, cl, ru, ss, hh}, t, x, h)))
        case Cr.Raw{y}:
          cft.keys_none(x, t, h)

def cft.keys_pick(b: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +x: Nat, +t: List<&2, Cr.Rec>, +eq: {Nat.is_eq(i, x) == b : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFile.claimed_spec(x, CronFileView.keys_of(t)) == cft.mclaimed(LCfd.cfd.first(x, t)) : Bool}) -> {CronFile.claimed_spec(x, CronFileView.keys_one(i, cl, CronFileView.keys_of(t))) == cft.mclaimed(LCfd.cfd.first.pick(b, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, LCfd.cfd.first(x, t))) : Bool}:
  match b:
    case True{}:
      match cl:
        case None{}:
          cft.keys_none(x, t, LCfd.cfd.has_move(i, x, t, LCfl.cfl.eq_of(i, x, eq), nt))
        case Some{c}:
          %Equal.sym(Bool, Nat.is_eq(x, i), True{}, Equal.trans(Bool, Nat.is_eq(x, i), Nat.is_eq(i, x), True{}, LCfl.cfl.eq_comm(x, i), eq)) : {Bool.or(_, CronFile.claimed_spec(x, CronFileView.keys_of(t))) == True{} : Bool}
          {==}
    case False{}:
      match cl:
        case None{}:
          ih
        case Some{c}:
          %Equal.sym(Bool, Nat.is_eq(x, i), False{}, Equal.trans(Bool, Nat.is_eq(x, i), Nat.is_eq(i, x), False{}, LCfl.cfl.eq_comm(x, i), eq)) : {Bool.or(_, CronFile.claimed_spec(x, CronFileView.keys_of(t))) == cft.mclaimed(LCfd.cfd.first(x, t)) : Bool}
          ih

# no two jobs share an id: a claim record names x exactly when the first
# job of id x has a claim on record
def cft.keys(+x: Nat, rs: List<&2, Cr.Rec>, +d: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFile.claimed_spec(x, CronFileView.keys_of(rs)) == cft.mclaimed(LCfd.cfd.first(x, rs)) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +h}:
              cft.keys_pick(Nat.is_eq(i, x), i, s, st, nx, k, cl, ru, ss, h, x, t, {==}, LCfd.cfd.distinct_head(Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, t, d), cft.keys(x, t, LCfd.cfd.distinct_tail(Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, t, d)))
        case Cr.Raw{y}:
          cft.keys(x, t, d)

# Rows
# ----

def cft.mrow(+x: Nat, m: Maybe<&2, Cr.Job>, +ks: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat, +u: Nat) -> Maybe<&2, CronFileView.FRow>:
  match m:
    case None{}:
      None{}
    case Some{+j}:
      Some{CronFileView.took_row(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(x, ks), d, n), j, u)}

def cft.took_head(a: CS.Took, j: Cr.Job, +x: Nat, +u: Nat, +rest: List<&2, CronFileView.FRow>) -> {CronFileView.row_at(x, CronFileView.took_row(a, j, u) <> rest) == CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.took_row(a, j, u), CronFileView.row_at(x, rest)) : Maybe<&2, CronFileView.FRow>}:
  match a:
    case CS.Keep{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Roll{nn}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Claimed{nn}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

def cft.rows_pick(b: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +ks: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat, +u: Nat, +x: Nat, eq: {Nat.is_eq(CronFileView.id_of(j), x) == b : Bool}, ih: {CronFileView.row_at(x, CronFileView.take_rows(t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), u)) == cft.mrow(x, LCfd.cfd.first(x, t), ks, d, n, u) : Maybe<&2, CronFileView.FRow>}) -> {CronFileView.row_at.pick(b, CronFileView.took_row(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(CronFileView.id_of(j), ks), d, n), j, u), CronFileView.row_at(x, CronFileView.take_rows(t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), u))) == cft.mrow(x, LCfd.cfd.first.pick(b, j, LCfd.cfd.first(x, t)), ks, d, n, u) : Maybe<&2, CronFileView.FRow>}:
  match b:
    case True{}:
      %LCfl.cfl.eq_of(CronFileView.id_of(j), x, eq) : {Some{CronFileView.took_row(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(CronFileView.id_of(j), ks), d, n), j, u)} == Some{CronFileView.took_row(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(_, ks), d, n), j, u)} : Maybe<&2, CronFileView.FRow>}
      {==}
    case False{}:
      ih

def cft.rows(+x: Nat, rs: List<&2, Cr.Rec>, +ks: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat, +u: Nat) -> {CronFileView.row_at(x, CronFileView.take_rows(rs, CronFile.take_all_spec(CronFileView.slots_of(rs, u), ks, d, n), u)) == cft.mrow(x, LCfd.cfd.first(x, rs), ks, d, n, u) : Maybe<&2, CronFileView.FRow>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          +a = CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(CronFileView.id_of(j), ks), d, n)
          +rest = CronFileView.take_rows(t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), u)
          %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.took_row(a, j, u) <> rest), CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.took_row(a, j, u), CronFileView.row_at(x, rest)), cft.took_head(a, j, x, u, rest)) : {_ == cft.mrow(x, LCfd.cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, LCfd.cfd.first(x, t)), ks, d, n, u) : Maybe<&2, CronFileView.FRow>}
          cft.rows_pick(Nat.is_eq(CronFileView.id_of(j), x), j, t, ks, d, n, u, x, {==}, cft.rows(x, t, ks, d, n, u))
        case Cr.Raw{y}:
          cft.rows(x, t, ks, d, n, u)

# The records this build cannot read
# ----------------------------------

def cft.raw_took(a: CS.Took, j: Cr.Job, +u: Nat, rest: List<&2, CronFileView.FRow>) -> {CronFileView.raw_rows(CronFileView.took_row(a, j, u) <> rest) == CronFileView.raw_rows(rest) : List<&2, Nat>}:
  match a:
    case CS.Keep{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Roll{nn}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Claimed{nn}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

def cft.raws(rs: List<&2, Cr.Rec>, ts: List<&2, CS.Took>, +u: Nat) -> {CronFileView.raw_rows(CronFileView.take_rows(rs, ts, u)) == CronFileView.raw_rows(CronFileView.rows_of(rs, u)) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          match ts:
            case Nil{}:
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.take_rows(t, Nil{}, u)), CronFileView.raw_rows(CronFileView.take_rows(t, Nil{}, u)), LCfd.cfd.raw_head(j, u, CronFileView.take_rows(t, Nil{}, u))) : {_ == CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)) : List<&2, Nat>}
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.raw_rows(CronFileView.rows_of(t, u)), LCfd.cfd.raw_head(j, u, CronFileView.rows_of(t, u))) : {CronFileView.raw_rows(CronFileView.take_rows(t, Nil{}, u)) == _ : List<&2, Nat>}
              cft.raws(t, Nil{}, u)
            case +a <> +rest:
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.took_row(a, j, u) <> CronFileView.take_rows(t, rest, u)), CronFileView.raw_rows(CronFileView.take_rows(t, rest, u)), cft.raw_took(a, j, u, CronFileView.take_rows(t, rest, u))) : {_ == CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)) : List<&2, Nat>}
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.raw_rows(CronFileView.rows_of(t, u)), LCfd.cfd.raw_head(j, u, CronFileView.rows_of(t, u))) : {CronFileView.raw_rows(CronFileView.take_rows(t, rest, u)) == _ : List<&2, Nat>}
              cft.raws(t, rest, u)
        case Cr.Raw{+y}:
          %cft.raws(t, ts, u) : {y <> CronFileView.raw_rows(CronFileView.take_rows(t, ts, u)) == y <> _ : List<&2, Nat>}
          {==}

# The claim records a claim pass adds
# -----------------------------------

# the claims of the record a claim pass of p adds for job j
def cft.new_cl(t: CS.Took, j: Cr.Job, +p: Nat, +u: Nat) -> List<&2, Cr.Claim>:
  match t:
    case CS.Keep{}:
      Nil{}
    case CS.Roll{nn}:
      Nil{}
    case CS.Claimed{nn}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          match nx:
            case None{}:
              Nil{}
            case Some{o}:
              [Cr.Claim{Nat.mul(o, u), p}]

def cft.mnew(+x: Nat, m: Maybe<&2, Cr.Job>, +ks: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat, +p: Nat, +u: Nat) -> List<&2, Cr.Claim>:
  match m:
    case None{}:
      Nil{}
    case Some{+j}:
      cft.new_cl(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(x, ks), d, n), j, p, u)

def cft.new_pick(b: Bool, l: List<&2, Cr.Claim>, r: List<&2, Cr.Claim>) -> List<&2, Cr.Claim>:
  match b:
    case True{}:
      List.append(&2, Cr.Claim, l, r)
    case False{}:
      r

def cft.pick_nil(b: Bool, +r: List<&2, Cr.Claim>) -> {r == cft.new_pick(b, Nil{}, r) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cft.pick_one(b: Bool, +c: Cr.Claim, +r: List<&2, Cr.Claim>) -> {CronFileView.marks_at.pick(b, c, r) == cft.new_pick(b, [c], r) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cft.new_at(a: CS.Took, j: Cr.Job, +p: Nat, +u: Nat, +x: Nat, +rest: List<&2, CronFileView.FClaim>, +b: Bool, eq: {Nat.is_eq(CronFileView.id_of(j), x) == b : Bool}) -> {CronFileView.marks_at(x, CronFileView.took_new(a, j, p, u, rest)) == cft.new_pick(b, cft.new_cl(a, j, p, u), CronFileView.marks_at(x, rest)) : List<&2, Cr.Claim>}:
  match a:
    case CS.Keep{}:
      cft.pick_nil(b, CronFileView.marks_at(x, rest))
    case CS.Roll{nn}:
      cft.pick_nil(b, CronFileView.marks_at(x, rest))
    case CS.Claimed{nn}:
      match j:
        case Cr.Job{+i, s, st, nx, k, cl, rs, ss, h}:
          match nx:
            case None{}:
              cft.pick_nil(b, CronFileView.marks_at(x, rest))
            case Some{+o}:
              %Equal.sym(Bool, Nat.is_eq(i, x), b, eq) : {CronFileView.marks_at.pick(_, Cr.Claim{Nat.mul(o, u), p}, CronFileView.marks_at(x, rest)) == cft.new_pick(b, [Cr.Claim{Nat.mul(o, u), p}], CronFileView.marks_at(x, rest)) : List<&2, Cr.Claim>}
              cft.pick_one(b, Cr.Claim{Nat.mul(o, u), p}, CronFileView.marks_at(x, rest))

def cft.news_none(+x: Nat, rs: List<&2, Cr.Rec>, ts: List<&2, CS.Took>, +p: Nat, +u: Nat, +h: {CronFileView.has_id(x, rs) == False{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.take_news(rs, ts, p, u)) == Nil{} : List<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          match ts:
            case Nil{}:
              cft.news_none(x, t, Nil{}, p, u, LCfd.cfd.has_tail(j, t, x, h))
            case +a <> +rest:
              %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.took_new(a, j, p, u, CronFileView.take_news(t, rest, p, u))), cft.new_pick(False{}, cft.new_cl(a, j, p, u), CronFileView.marks_at(x, CronFileView.take_news(t, rest, p, u))), cft.new_at(a, j, p, u, x, CronFileView.take_news(t, rest, p, u), False{}, LCfd.cfd.has_head(j, t, x, h))) : {_ == Nil{} : List<&2, Cr.Claim>}
              cft.news_none(x, t, rest, p, u, LCfd.cfd.has_tail(j, t, x, h))
        case Cr.Raw{y}:
          cft.news_none(x, t, ts, p, u, h)

def cft.app_nil(l: List<&2, Cr.Claim>) -> {List.append(&2, Cr.Claim, l, Nil{}) == l : List<&2, Cr.Claim>}:
  match l:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(List<&2, Cr.Claim>, List.append(&2, Cr.Claim, t, Nil{}), t, cft.app_nil(t)) : {c <> _ == c <> t : List<&2, Cr.Claim>}
      {==}

def cft.news_pick(b: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +ks: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat, +p: Nat, +u: Nat, +x: Nat, eq: {Nat.is_eq(CronFileView.id_of(j), x) == b : Bool}, nt: {CronFileView.has_id(CronFileView.id_of(j), t) == False{} : Bool}, ih: {CronFileView.marks_at(x, CronFileView.take_news(t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), p, u)) == cft.mnew(x, LCfd.cfd.first(x, t), ks, d, n, p, u) : List<&2, Cr.Claim>}) -> {cft.new_pick(b, cft.new_cl(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(CronFileView.id_of(j), ks), d, n), j, p, u), CronFileView.marks_at(x, CronFileView.take_news(t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), p, u))) == cft.mnew(x, LCfd.cfd.first.pick(b, j, LCfd.cfd.first(x, t)), ks, d, n, p, u) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      +ix = LCfl.cfl.eq_of(CronFileView.id_of(j), x, eq)
      +l = cft.new_cl(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(CronFileView.id_of(j), ks), d, n), j, p, u)
      %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.take_news(t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), p, u)), Nil{}, cft.news_none(x, t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), p, u, LCfd.cfd.has_move(CronFileView.id_of(j), x, t, ix, nt))) : {List.append(&2, Cr.Claim, l, _) == cft.mnew(x, Some{j}, ks, d, n, p, u) : List<&2, Cr.Claim>}
      %Equal.sym(List<&2, Cr.Claim>, List.append(&2, Cr.Claim, l, Nil{}), l, cft.app_nil(l)) : {_ == cft.mnew(x, Some{j}, ks, d, n, p, u) : List<&2, Cr.Claim>}
      %ix : {l == cft.new_cl(CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(_, ks), d, n), j, p, u) : List<&2, Cr.Claim>}
      {==}
    case False{}:
      ih

def cft.news(+x: Nat, rs: List<&2, Cr.Rec>, +ks: List<&2, Maybe<&2, Nat>>, +d: Nat, +n: Nat, +p: Nat, +u: Nat, +dd: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.take_news(rs, CronFile.take_all_spec(CronFileView.slots_of(rs, u), ks, d, n), p, u)) == cft.mnew(x, LCfd.cfd.first(x, rs), ks, d, n, p, u) : List<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          +a = CronStore.take_spec(Cron.fact_of(j, u), CronFile.claimed_spec(CronFileView.id_of(j), ks), d, n)
          +rest = CronFileView.take_news(t, CronFile.take_all_spec(CronFileView.slots_of(t, u), ks, d, n), p, u)
          %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.took_new(a, j, p, u, rest)), cft.new_pick(Nat.is_eq(CronFileView.id_of(j), x), cft.new_cl(a, j, p, u), CronFileView.marks_at(x, rest)), cft.new_at(a, j, p, u, x, rest, Nat.is_eq(CronFileView.id_of(j), x), {==})) : {_ == cft.mnew(x, LCfd.cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, LCfd.cfd.first(x, t)), ks, d, n, p, u) : List<&2, Cr.Claim>}
          cft.news_pick(Nat.is_eq(CronFileView.id_of(j), x), j, t, ks, d, n, p, u, x, {==}, LCfd.cfd.distinct_head(j, t, dd), cft.news(x, t, ks, d, n, p, u, LCfd.cfd.distinct_tail(j, t, dd)))
        case Cr.Raw{y}:
          cft.news(x, t, ks, d, n, p, u, dd)

# One job, against cron_take_refines
# ----------------------------------

def cft.row_took(t: CS.Took, j: Cr.Job, +p: Nat, +u: Nat) -> {CronFileView.took_row(t, j, u) == LCfd.cfd.prow(CronFileView.id_of(j), Cron.took_view(t, j, p, u)) : CronFileView.FRow}:
  match t:
    case CS.Keep{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Roll{nn}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Claimed{nn}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

# a job with no claim on record: its records are the one a claim adds
def cft.mt_none(t: CS.Took, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +u: Nat) -> {List.append(&2, Cr.Claim, Nil{}, cft.new_cl(t, Cr.Job{i, s, st, nx, k, None{}, rs, ss, h}, p, u)) == LCfd.cfd.pcl(Cron.took_view(t, Cr.Job{i, s, st, nx, k, None{}, rs, ss, h}, p, u)) : List<&2, Cr.Claim>}:
  match t:
    case CS.Keep{}:
      {==}
    case CS.Roll{nn}:
      {==}
    case CS.Claimed{nn}:
      match nx:
        case None{}:
          {==}
        case Some{o}:
          {==}

def cft.mt_due(b: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +u: Nat, +pl: CS.Plan, +n: Nat) -> {List.append(&2, Cr.Claim, LCfd.cfd.own_cl(Some{x}, u), cft.new_cl(CronStore.take_spec.due(b, True{}, pl, n), Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}, p, u)) == LCfd.cfd.pcl(Cron.took_view(CronStore.take_spec.due(b, True{}, pl, n), Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}, p, u)) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      match x:
        case Cr.Claim{o, w}:
          {==}
    case False{}:
      match x:
        case Cr.Claim{o, w}:
          {==}

# a job with a claim on record: a claim pass only keeps or rolls it
def cft.mt_some(+i: Nat, +s: Cr.Sched, st: Cr.Status, nx: Maybe<&2, Nat>, +k: Nat, +x: Cr.Claim, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +u: Nat, +d: Nat, +n: Nat) -> {List.append(&2, Cr.Claim, LCfd.cfd.own_cl(Some{x}, u), cft.new_cl(CronStore.take_spec(Cron.fact_of(Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}, u), True{}, d, n), Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}, p, u)) == LCfd.cfd.pcl(Cron.took_view(CronStore.take_spec(Cron.fact_of(Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}, u), True{}, d, n), Cr.Job{i, s, st, nx, k, Some{x}, rs, ss, h}, p, u)) : List<&2, Cr.Claim>}:
  match st:
    case Cr.Active{}:
      match nx:
        case None{}:
          match x:
            case Cr.Claim{o, w}:
              {==}
        case Some{+o}:
          cft.mt_due(Nat.is_le(Nat.mul(o, u), d), i, s, Cr.Active{}, Some{o}, k, x, rs, ss, h, p, u, Cron.plan_of(s, u), n)
    case Cr.Paused{}:
      match x:
        case Cr.Claim{o, w}:
          {==}
    case Cr.Finished{}:
      match x:
        case Cr.Claim{o, w}:
          {==}
    case Cr.Cancelled{}:
      match x:
        case Cr.Claim{o, w}:
          {==}

def cft.marks_took(j: Cr.Job, +d: Nat, +n: Nat, +p: Nat, +u: Nat) -> {List.append(&2, Cr.Claim, LCfd.cfd.own(j, u), cft.new_cl(CronStore.take_spec(Cron.fact_of(j, u), Cron.claimed_of(j), d, n), j, p, u)) == LCfd.cfd.pcl(Cron.took_view(CronStore.take_spec(Cron.fact_of(j, u), Cron.claimed_of(j), d, n), j, p, u)) : List<&2, Cr.Claim>}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, cl, +rs, +ss, +h}:
      match cl:
        case None{}:
          cft.mt_none(CronStore.take_spec(Cron.fact_of(Cr.Job{i, s, st, nx, k, None{}, rs, ss, h}, u), False{}, d, n), i, s, st, nx, k, rs, ss, h, p, u)
        case Some{+x}:
          cft.mt_some(i, s, st, nx, k, x, rs, ss, h, p, u, d, n)

def cft.some(+v: Nat, +p: Nat, +c: Nat, +j: Cr.Job, +r3: List<&2, Nat>, +rd: List<&2, Nat>) -> {(Some{CronFileView.took_row(CronStore.take_spec(Cron.fact_of(j, 1n+v), Cron.claimed_of(j), Nat.mul(c, 1n+v), Nat.mul(c, 1n+v)), j, 1n+v)}, (List.append(&2, Cr.Claim, LCfd.cfd.own(j, 1n+v), cft.new_cl(CronStore.take_spec(Cron.fact_of(j, 1n+v), Cron.claimed_of(j), Nat.mul(c, 1n+v), Nat.mul(c, 1n+v)), j, p, 1n+v)), (r3, rd))) == (Some{CronFileView.row_of(Cr.take(p, c, j), 1n+v)}, (LCfd.cfd.own(Cr.take(p, c, j), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  +u = {1n+v : Nat}
  +t = CronStore.take_spec(Cron.fact_of(j, u), Cron.claimed_of(j), Nat.mul(c, u), Nat.mul(c, u))
  -tv = Cron.took_view(t, j, p, u)
  -vv = Cron.view(Cr.take(p, c, j), u)
  %Equal.sym(CronFileView.FRow, CronFileView.took_row(t, j, u), LCfd.cfd.prow(CronFileView.id_of(j), tv), cft.row_took(t, j, p, u)) : {(Some{_}, (List.append(&2, Cr.Claim, LCfd.cfd.own(j, u), cft.new_cl(t, j, p, u)), (r3, rd))) == (Some{CronFileView.row_of(Cr.take(p, c, j), u)}, (LCfd.cfd.own(Cr.take(p, c, j), u), (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, List.append(&2, Cr.Claim, LCfd.cfd.own(j, u), cft.new_cl(t, j, p, u)), LCfd.cfd.pcl(tv), cft.marks_took(j, Nat.mul(c, u), Nat.mul(c, u), p, u)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), tv)}, (_, (r3, rd))) == (Some{CronFileView.row_of(Cr.take(p, c, j), u)}, (LCfd.cfd.own(Cr.take(p, c, j), u), (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(CronFileView.FRow, CronFileView.row_of(Cr.take(p, c, j), u), LCfd.cfd.prow(CronFileView.id_of(Cr.take(p, c, j)), vv), LCfd.cfd.row_view(Cr.take(p, c, j), u)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), tv)}, (LCfd.cfd.pcl(tv), (r3, rd))) == (Some{_}, (LCfd.cfd.own(Cr.take(p, c, j), u), (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, LCfd.cfd.own(Cr.take(p, c, j), u), LCfd.cfd.pcl(vv), LCfd.cfd.own_view(Cr.take(p, c, j), u)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), tv)}, (LCfd.cfd.pcl(tv), (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(Cr.take(p, c, j)), vv)}, (_, (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(Nat, CronFileView.id_of(Cr.job(Cr.Take{p}, c, Nil{}, j)), CronFileView.id_of(j), LCfd.cfd.id_job(Cr.Take{p}, c, Nil{}, j)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), tv)}, (LCfd.cfd.pcl(tv), (r3, rd))) == (Some{LCfd.cfd.prow(_, vv)}, (LCfd.cfd.pcl(vv), (r3, rd))) : CronFileView.Obs()}
  %Cron.cron_take_refines(v, p, c, j) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), tv)}, (LCfd.cfd.pcl(tv), (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(j), _)}, (LCfd.cfd.pcl(_), (r3, rd))) : CronFileView.Obs()}
  {==}

def cft.final(+v: Nat, +p: Nat, +c: Nat, +x: Nat, +dead: List<&2, Nat>, m: Maybe<&2, Cr.Job>, +r3: List<&2, Nat>, +rd: List<&2, Nat>, +ks: List<&2, Maybe<&2, Nat>>, kx: {CronFile.claimed_spec(x, ks) == cft.mclaimed(m) : Bool}) -> {(cft.mrow(x, m, ks, Nat.mul(c, 1n+v), Nat.mul(c, 1n+v), 1n+v), (List.append(&2, Cr.Claim, LCfd.cfd.mclaims(m, 1n+v), cft.mnew(x, m, ks, Nat.mul(c, 1n+v), Nat.mul(c, 1n+v), p, 1n+v)), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Take{p}, c, dead, m), 1n+v), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Take{p}, c, dead, m), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      %Equal.sym(Bool, CronFile.claimed_spec(x, ks), Cron.claimed_of(j), kx) : {(Some{CronFileView.took_row(CronStore.take_spec(Cron.fact_of(j, 1n+v), _, Nat.mul(c, 1n+v), Nat.mul(c, 1n+v)), j, 1n+v)}, (List.append(&2, Cr.Claim, LCfd.cfd.own(j, 1n+v), cft.new_cl(CronStore.take_spec(Cron.fact_of(j, 1n+v), _, Nat.mul(c, 1n+v), Nat.mul(c, 1n+v)), j, p, 1n+v)), (r3, rd))) == (Some{CronFileView.row_of(Cr.take(p, c, j), 1n+v)}, (LCfd.cfd.own(Cr.take(p, c, j), 1n+v), (r3, rd))) : CronFileView.Obs()}
      cft.some(v, p, c, j, r3, rd)

def CronFileView.cron_file_take_refines(v, p, c, x, dead, rs, rd, ok0):
  +ok = ok0
  +u = {1n+v : Nat}
  +cu = Nat.mul(c, u)
  +ks = CronFileView.keys_of(rs)
  +ts = CronFile.take_all_spec(CronFileView.slots_of(rs, u), ks, cu, cu)
  +rr = Cr.recs(Cr.Take{p}, c, dead, rs)
  +f = LCfd.cfd.first(x, rs)
  -mr = cft.mrow(x, f, ks, cu, cu, u)
  -ma = CronFileView.marks_at(x, CronFileView.marks_of(rs, u))
  -mn = CronFileView.marks_at(x, CronFileView.take_news(rs, ts, p, u))
  +r3 = CronFileView.raw_rows(CronFileView.rows_of(rs, u))
  +drr = Equal.trans(Bool, CronFileView.distinct(rr), CronFileView.distinct(rs), True{}, LCfd.cfd.distinct_recs(Cr.Take{p}, c, dead, rs), ok)
  %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.take_rows(rs, ts, u)), mr, cft.rows(x, rs, ks, cu, cu, u)) : {(_, (CronFileView.marks_at(x, List.append(&2, CronFileView.FClaim, CronFileView.marks_of(rs, u), CronFileView.take_news(rs, ts, p, u))), (CronFileView.raw_rows(CronFileView.take_rows(rs, ts, u)), rd))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, List.append(&2, CronFileView.FClaim, CronFileView.marks_of(rs, u), CronFileView.take_news(rs, ts, p, u))), List.append(&2, Cr.Claim, ma, mn), LCfd.cfd.marks_app(x, CronFileView.marks_of(rs, u), CronFileView.take_news(rs, ts, p, u))) : {(mr, (_, (CronFileView.raw_rows(CronFileView.take_rows(rs, ts, u)), rd))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, ma, LCfd.cfd.mclaims(f, u), LCfd.cfd.marks_at(x, rs, u, ok)) : {(mr, (List.append(&2, Cr.Claim, _, mn), (CronFileView.raw_rows(CronFileView.take_rows(rs, ts, u)), rd))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, mn, cft.mnew(x, f, ks, cu, cu, p, u), cft.news(x, rs, ks, cu, cu, p, u, ok)) : {(mr, (List.append(&2, Cr.Claim, LCfd.cfd.mclaims(f, u), _), (CronFileView.raw_rows(CronFileView.take_rows(rs, ts, u)), rd))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.take_rows(rs, ts, u)), r3, cft.raws(rs, ts, u)) : {(mr, (List.append(&2, Cr.Claim, LCfd.cfd.mclaims(f, u), cft.mnew(x, f, ks, cu, cu, p, u)), (_, rd))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.rows_of(rr, u)), LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), LCfd.cfd.rows_at(x, rr, u)) : {(mr, (List.append(&2, Cr.Claim, LCfd.cfd.mclaims(f, u), cft.mnew(x, f, ks, cu, cu, p, u)), (r3, rd))) == (_, (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), LCfd.cfd.mclaims(LCfd.cfd.first(x, rr), u), LCfd.cfd.marks_at(x, rr, u, drr)) : {(mr, (List.append(&2, Cr.Claim, LCfd.cfd.mclaims(f, u), cft.mnew(x, f, ks, cu, cu, p, u)), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), (_, (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.rows_of(rr, u)), r3, LCfd.cfd.raws_recs(Cr.Take{p}, c, dead, rs, u)) : {(mr, (List.append(&2, Cr.Claim, LCfd.cfd.mclaims(f, u), cft.mnew(x, f, ks, cu, cu, p, u)), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), (LCfd.cfd.mclaims(LCfd.cfd.first(x, rr), u), (_, rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, Cr.Job>, LCfd.cfd.first(x, rr), LCfd.cfd.mapj(Cr.Take{p}, c, dead, f), LCfd.cfd.first_recs(Cr.Take{p}, c, dead, rs, x)) : {(mr, (List.append(&2, Cr.Claim, LCfd.cfd.mclaims(f, u), cft.mnew(x, f, ks, cu, cu, p, u)), (r3, rd))) == (LCfd.cfd.mrow(_, u), (LCfd.cfd.mclaims(_, u), (r3, rd))) : CronFileView.Obs()}
  cft.final(v, p, c, x, dead, f, r3, rd, ks, cft.keys(x, rs, ok))
