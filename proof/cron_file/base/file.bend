# eukhe: lemmas the proofs of area cron_file share: the file as the store
# holds it (laws/cron_file.bend `file_of`), read job by job. The first job
# record of id x (`cfd.first`) decides what the file holds of x: its row,
# and (when no two jobs share an id) the claim records naming x. The
# model's `recs` keeps every id, so the first job of id x after a step is
# the step of the first job of id x before it.

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../laws/cron.bend as Cron
import ../../../laws/cron_store.bend as CronStore
import ../../../laws/cron_file/pass.bend as CronFile
import ../../../laws/cron_file/entry.bend as CronFileEntry
import ../../../laws/cron_file/view.bend as CronFileView
import ../../cron/base/cron.bend as LACron
import ./logic.bend as LCfl

# The first job of an id
# ----------------------

def cfd.first.pick(b: Bool, j: Cr.Job, rest: Maybe<&2, Cr.Job>) -> Maybe<&2, Cr.Job>:
  match b:
    case True{}:
      Some{j}
    case False{}:
      rest

# the first job record of id x
def cfd.first(+x: Nat, rs: List<&2, Cr.Rec>) -> Maybe<&2, Cr.Job>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      match r:
        case Cr.Known{+j}:
          cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, cfd.first(x, t))
        case Cr.Raw{y}:
          cfd.first(x, t)

def cfd.mapj(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, m: Maybe<&2, Cr.Job>) -> Maybe<&2, Cr.Job>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Some{Cr.job(e, c, dead, j)}

def cfd.mrow(m: Maybe<&2, Cr.Job>, +u: Nat) -> Maybe<&2, CronFileView.FRow>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Some{CronFileView.row_of(j, u)}

# a claim on record, as the claims of the records naming its job
def cfd.own_cl(cl: Maybe<&2, Cr.Claim>, +u: Nat) -> List<&2, Cr.Claim>:
  match cl:
    case None{}:
      Nil{}
    case Some{x}:
      match x:
        case Cr.Claim{o, w}:
          [Cr.Claim{Nat.mul(o, u), w}]

def cfd.own(j: Cr.Job, +u: Nat) -> List<&2, Cr.Claim>:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      cfd.own_cl(cl, u)

def cfd.mclaims(m: Maybe<&2, Cr.Job>, +u: Nat) -> List<&2, Cr.Claim>:
  match m:
    case None{}:
      Nil{}
    case Some{j}:
      cfd.own(j, u)

# Ids
# ---

def cfd.id_eq(j: Cr.Job) -> {CronFileView.id_of(j) == Cr.Job.id(j) : Nat}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

# a step keeps a job's id
def cfd.id_job(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job) -> {CronFileView.id_of(Cr.job(e, c, dead, j)) == CronFileView.id_of(j) : Nat}:
  %Equal.sym(Nat, CronFileView.id_of(Cr.job(e, c, dead, j)), Cr.Job.id(Cr.job(e, c, dead, j)), cfd.id_eq(Cr.job(e, c, dead, j))) : {_ == CronFileView.id_of(j) : Nat}
  %Equal.sym(Nat, CronFileView.id_of(j), Cr.Job.id(j), cfd.id_eq(j)) : {Cr.Job.id(Cr.job(e, c, dead, j)) == _ : Nat}
  LACron.pc.id_job(e, c, dead, j)

# Splitting Bools
# ---------------

def cfd.distinct_head(+j: Cr.Job, +t: List<&2, Cr.Rec>, d: {CronFileView.distinct(Cr.Known{j} <> t) == True{} : Bool}) -> {CronFileView.has_id(CronFileView.id_of(j), t) == False{} : Bool}:
  LCfl.cfl.not_true(CronFileView.has_id(CronFileView.id_of(j), t), LCfl.cfl.and_l(Bool.not(CronFileView.has_id(CronFileView.id_of(j), t)), CronFileView.distinct(t), d))

def cfd.distinct_tail(+j: Cr.Job, +t: List<&2, Cr.Rec>, d: {CronFileView.distinct(Cr.Known{j} <> t) == True{} : Bool}) -> {CronFileView.distinct(t) == True{} : Bool}:
  LCfl.cfl.and_r(Bool.not(CronFileView.has_id(CronFileView.id_of(j), t)), CronFileView.distinct(t), d)

def cfd.has_head(+j: Cr.Job, +t: List<&2, Cr.Rec>, +x: Nat, h: {CronFileView.has_id(x, Cr.Known{j} <> t) == False{} : Bool}) -> {Nat.is_eq(CronFileView.id_of(j), x) == False{} : Bool}:
  LCfl.cfl.or_false_l(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.has_id(x, t), h)

def cfd.has_tail(+j: Cr.Job, +t: List<&2, Cr.Rec>, +x: Nat, h: {CronFileView.has_id(x, Cr.Known{j} <> t) == False{} : Bool}) -> {CronFileView.has_id(x, t) == False{} : Bool}:
  LCfl.cfl.or_false_r(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.has_id(x, t), h)

# A file's rows
# -------------

def cfd.rows_pick(b: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +x: Nat, +u: Nat, ih: {CronFileView.row_at(x, CronFileView.rows_of(t, u)) == cfd.mrow(cfd.first(x, t), u) : Maybe<&2, CronFileView.FRow>}) -> {CronFileView.row_at.pick(b, CronFileView.row_of(j, u), CronFileView.row_at(x, CronFileView.rows_of(t, u))) == cfd.mrow(cfd.first.pick(b, j, cfd.first(x, t)), u) : Maybe<&2, CronFileView.FRow>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def cfd.row_at_head(+j: Cr.Job, +x: Nat, +u: Nat, +rest: List<&2, CronFileView.FRow>) -> {CronFileView.row_at(x, CronFileView.row_of(j, u) <> rest) == CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.row_of(j, u), CronFileView.row_at(x, rest)) : Maybe<&2, CronFileView.FRow>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

# the file holds the first job of id x as its row
def cfd.rows_at(+x: Nat, rs: List<&2, Cr.Rec>, +u: Nat) -> {CronFileView.row_at(x, CronFileView.rows_of(rs, u)) == cfd.mrow(cfd.first(x, rs), u) : Maybe<&2, CronFileView.FRow>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.row_of(j, u), CronFileView.row_at(x, CronFileView.rows_of(t, u))), cfd.row_at_head(j, x, u, CronFileView.rows_of(t, u))) : {_ == cfd.mrow(cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, cfd.first(x, t)), u) : Maybe<&2, CronFileView.FRow>}
          cfd.rows_pick(Nat.is_eq(CronFileView.id_of(j), x), j, t, x, u, cfd.rows_at(x, t, u))
        case Cr.Raw{y}:
          cfd.rows_at(x, t, u)

# the job records this build cannot read are the file's
def cfd.raw_head(+j: Cr.Job, +u: Nat, rest: List<&2, CronFileView.FRow>) -> {CronFileView.raw_rows(CronFileView.row_of(j, u) <> rest) == CronFileView.raw_rows(rest) : List<&2, Nat>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

def cfd.raws_recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +u: Nat) -> {CronFileView.raw_rows(CronFileView.rows_of(Cr.recs(e, c, dead, rs), u)) == CronFileView.raw_rows(CronFileView.rows_of(rs, u)) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.raw_rows(CronFileView.rows_of(t, u)), cfd.raw_head(j, u, CronFileView.rows_of(t, u))) : {CronFileView.raw_rows(CronFileView.rows_of(Cr.recs(e, c, dead, Cr.Known{j} <> t), u)) == _ : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(Cr.job(e, c, dead, j), u) <> CronFileView.rows_of(Cr.recs(e, c, dead, t), u)), CronFileView.raw_rows(CronFileView.rows_of(Cr.recs(e, c, dead, t), u)), cfd.raw_head(Cr.job(e, c, dead, j), u, CronFileView.rows_of(Cr.recs(e, c, dead, t), u))) : {_ == CronFileView.raw_rows(CronFileView.rows_of(t, u)) : List<&2, Nat>}
          cfd.raws_recs(e, c, dead, t, u)
        case Cr.Raw{+y}:
          %cfd.raws_recs(e, c, dead, t, u) : {y <> CronFileView.raw_rows(CronFileView.rows_of(Cr.recs(e, c, dead, t), u)) == y <> _ : List<&2, Nat>}
          {==}

# A file's claim records
# ----------------------

def cfd.marks_none_one(+i: Nat, cl: Maybe<&2, Cr.Claim>, +u: Nat, +x: Nat, +rest: List<&2, CronFileView.FClaim>, ne: {Nat.is_eq(i, x) == False{} : Bool}, ih: {CronFileView.marks_at(x, rest) == Nil{} : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.marks_one(i, cl, u, rest)) == Nil{} : List<&2, Cr.Claim>}:
  match cl:
    case None{}:
      ih
    case Some{c}:
      match c:
        case Cr.Claim{o, w}:
          %Equal.sym(Bool, Nat.is_eq(i, x), False{}, ne) : {CronFileView.marks_at.pick(_, Cr.Claim{Nat.mul(o, u), w}, CronFileView.marks_at(x, rest)) == Nil{} : List<&2, Cr.Claim>}
          ih

# no job of id x: no claim record names x
def cfd.marks_none(+x: Nat, rs: List<&2, Cr.Rec>, +u: Nat, +h: {CronFileView.has_id(x, rs) == False{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.marks_of(rs, u)) == Nil{} : List<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +hh}:
              +ne = cfd.has_head(Cr.Job{i, s, st, nx, k, cl, ru, ss, hh}, t, x, h)
              +ht = cfd.has_tail(Cr.Job{i, s, st, nx, k, cl, ru, ss, hh}, t, x, h)
              cfd.marks_none_one(i, cl, u, x, CronFileView.marks_of(t, u), ne, cfd.marks_none(x, t, u, ht))
        case Cr.Raw{y}:
          cfd.marks_none(x, t, u, h)

def cfd.own_none(+i: Nat, cl: Maybe<&2, Cr.Claim>, +u: Nat, +x: Nat, +rest: List<&2, CronFileView.FClaim>, eq: {Nat.is_eq(i, x) == True{} : Bool}, tl: {CronFileView.marks_at(x, rest) == Nil{} : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.marks_one(i, cl, u, rest)) == cfd.own_cl(cl, u) : List<&2, Cr.Claim>}:
  match cl:
    case None{}:
      tl
    case Some{c}:
      match c:
        case Cr.Claim{o, w}:
          %Equal.sym(Bool, Nat.is_eq(i, x), True{}, eq) : {CronFileView.marks_at.pick(_, Cr.Claim{Nat.mul(o, u), w}, CronFileView.marks_at(x, rest)) == [Cr.Claim{Nat.mul(o, u), w}] : List<&2, Cr.Claim>}
          %tl : {Cr.Claim{Nat.mul(o, u), w} <> CronFileView.marks_at(x, rest) == Cr.Claim{Nat.mul(o, u), w} <> _ : List<&2, Cr.Claim>}
          {==}

def cfd.marks_skip(+i: Nat, cl: Maybe<&2, Cr.Claim>, +u: Nat, +x: Nat, +rest: List<&2, CronFileView.FClaim>, ne: {Nat.is_eq(i, x) == False{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.marks_one(i, cl, u, rest)) == CronFileView.marks_at(x, rest) : List<&2, Cr.Claim>}:
  match cl:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case Cr.Claim{o, w}:
          %Equal.sym(Bool, Nat.is_eq(i, x), False{}, ne) : {CronFileView.marks_at.pick(_, Cr.Claim{Nat.mul(o, u), w}, CronFileView.marks_at(x, rest)) == CronFileView.marks_at(x, rest) : List<&2, Cr.Claim>}
          {==}

# an id equal to x carries what is known of x
def cfd.has_move(+i: Nat, +x: Nat, +t: List<&2, Cr.Rec>, ix: {i == x : Nat}, nt: {CronFileView.has_id(i, t) == False{} : Bool}) -> {CronFileView.has_id(x, t) == False{} : Bool}:
  Equal.trans(Bool, CronFileView.has_id(x, t), CronFileView.has_id(i, t), False{}, Equal.sym(Bool, CronFileView.has_id(i, t), CronFileView.has_id(x, t), Equal.cong(Nat, Bool, y => CronFileView.has_id(y, t), i, x, ix)), nt)

def cfd.marks_pick(b: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +u: Nat, +x: Nat, +t: List<&2, Cr.Rec>, +eq: {Nat.is_eq(i, x) == b : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFileView.marks_at(x, CronFileView.marks_of(t, u)) == cfd.mclaims(cfd.first(x, t), u) : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.marks_one(i, cl, u, CronFileView.marks_of(t, u))) == cfd.mclaims(cfd.first.pick(b, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, cfd.first(x, t)), u) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      cfd.own_none(i, cl, u, x, CronFileView.marks_of(t, u), eq, cfd.marks_none(x, t, u, cfd.has_move(i, x, t, LCfl.cfl.eq_of(i, x, eq), nt)))
    case False{}:
      %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.marks_one(i, cl, u, CronFileView.marks_of(t, u))), CronFileView.marks_at(x, CronFileView.marks_of(t, u)), cfd.marks_skip(i, cl, u, x, CronFileView.marks_of(t, u), eq)) : {_ == cfd.mclaims(cfd.first(x, t), u) : List<&2, Cr.Claim>}
      ih

# no two jobs share an id: the claim records naming x are the first job's
def cfd.marks_at(+x: Nat, rs: List<&2, Cr.Rec>, +u: Nat, +d: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.marks_of(rs, u)) == cfd.mclaims(cfd.first(x, rs), u) : List<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +h}:
              cfd.marks_pick(Nat.is_eq(i, x), i, s, st, nx, k, cl, ru, ss, h, u, x, t, {==}, cfd.distinct_head(Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, t, d), cfd.marks_at(x, t, u, cfd.distinct_tail(Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, t, d)))
        case Cr.Raw{y}:
          cfd.marks_at(x, t, u, d)

# a step keeps every id
def cfd.first_pick(b: Bool, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +t: List<&2, Cr.Rec>, +x: Nat, ih: {cfd.first(x, Cr.recs(e, c, dead, t)) == cfd.mapj(e, c, dead, cfd.first(x, t)) : Maybe<&2, Cr.Job>}) -> {cfd.first.pick(b, Cr.job(e, c, dead, j), cfd.first(x, Cr.recs(e, c, dead, t))) == cfd.mapj(e, c, dead, cfd.first.pick(b, j, cfd.first(x, t))) : Maybe<&2, Cr.Job>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def cfd.first_recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +x: Nat) -> {cfd.first(x, Cr.recs(e, c, dead, rs)) == cfd.mapj(e, c, dead, cfd.first(x, rs)) : Maybe<&2, Cr.Job>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Nat, CronFileView.id_of(Cr.job(e, c, dead, j)), CronFileView.id_of(j), cfd.id_job(e, c, dead, j)) : {cfd.first.pick(Nat.is_eq(_, x), Cr.job(e, c, dead, j), cfd.first(x, Cr.recs(e, c, dead, t))) == cfd.mapj(e, c, dead, cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, cfd.first(x, t))) : Maybe<&2, Cr.Job>}
          cfd.first_pick(Nat.is_eq(CronFileView.id_of(j), x), e, c, dead, j, t, x, cfd.first_recs(e, c, dead, t, x))
        case Cr.Raw{y}:
          cfd.first_recs(e, c, dead, t, x)

def cfd.has_recs(+x: Nat, +e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> {CronFileView.has_id(x, Cr.recs(e, c, dead, rs)) == CronFileView.has_id(x, rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Nat, CronFileView.id_of(Cr.job(e, c, dead, j)), CronFileView.id_of(j), cfd.id_job(e, c, dead, j)) : {Bool.or(Nat.is_eq(_, x), CronFileView.has_id(x, Cr.recs(e, c, dead, t))) == Bool.or(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.has_id(x, t)) : Bool}
          %Equal.sym(Bool, CronFileView.has_id(x, Cr.recs(e, c, dead, t)), CronFileView.has_id(x, t), cfd.has_recs(x, e, c, dead, t)) : {Bool.or(Nat.is_eq(CronFileView.id_of(j), x), _) == Bool.or(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.has_id(x, t)) : Bool}
          {==}
        case Cr.Raw{y}:
          cfd.has_recs(x, e, c, dead, t)

def cfd.distinct_recs(+e: Cr.Ev, +c: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>) -> {CronFileView.distinct(Cr.recs(e, c, dead, rs)) == CronFileView.distinct(rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(Nat, CronFileView.id_of(Cr.job(e, c, dead, j)), CronFileView.id_of(j), cfd.id_job(e, c, dead, j)) : {Bool.and(Bool.not(CronFileView.has_id(_, Cr.recs(e, c, dead, t))), CronFileView.distinct(Cr.recs(e, c, dead, t))) == Bool.and(Bool.not(CronFileView.has_id(CronFileView.id_of(j), t)), CronFileView.distinct(t)) : Bool}
          %Equal.sym(Bool, CronFileView.has_id(CronFileView.id_of(j), Cr.recs(e, c, dead, t)), CronFileView.has_id(CronFileView.id_of(j), t), cfd.has_recs(CronFileView.id_of(j), e, c, dead, t)) : {Bool.and(Bool.not(_), CronFileView.distinct(Cr.recs(e, c, dead, t))) == Bool.and(Bool.not(CronFileView.has_id(CronFileView.id_of(j), t)), CronFileView.distinct(t)) : Bool}
          %Equal.sym(Bool, CronFileView.distinct(Cr.recs(e, c, dead, t)), CronFileView.distinct(t), cfd.distinct_recs(e, c, dead, t)) : {Bool.and(Bool.not(CronFileView.has_id(CronFileView.id_of(j), t)), _) == Bool.and(Bool.not(CronFileView.has_id(CronFileView.id_of(j), t)), CronFileView.distinct(t)) : Bool}
          {==}
        case Cr.Raw{y}:
          cfd.distinct_recs(e, c, dead, t)

def cfd.marks_app_pick(b: Bool, +cl: Cr.Claim, +x: Nat, +t: List<&2, CronFileView.FClaim>, +bb: List<&2, CronFileView.FClaim>, ih: {CronFileView.marks_at(x, List.append(&2, CronFileView.FClaim, t, bb)) == List.append(&2, Cr.Claim, CronFileView.marks_at(x, t), CronFileView.marks_at(x, bb)) : List<&2, Cr.Claim>}) -> {CronFileView.marks_at.pick(b, cl, CronFileView.marks_at(x, List.append(&2, CronFileView.FClaim, t, bb))) == List.append(&2, Cr.Claim, CronFileView.marks_at.pick(b, cl, CronFileView.marks_at(x, t)), CronFileView.marks_at(x, bb)) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, List.append(&2, CronFileView.FClaim, t, bb)), List.append(&2, Cr.Claim, CronFileView.marks_at(x, t), CronFileView.marks_at(x, bb)), ih) : {cl <> _ == cl <> List.append(&2, Cr.Claim, CronFileView.marks_at(x, t), CronFileView.marks_at(x, bb)) : List<&2, Cr.Claim>}
      {==}
    case False{}:
      ih

def cfd.marks_app(+x: Nat, a: List<&2, CronFileView.FClaim>, +b: List<&2, CronFileView.FClaim>) -> {CronFileView.marks_at(x, List.append(&2, CronFileView.FClaim, a, b)) == List.append(&2, Cr.Claim, CronFileView.marks_at(x, a), CronFileView.marks_at(x, b)) : List<&2, Cr.Claim>}:
  match a:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case CronFileView.FClaim{i, +cl}:
          cfd.marks_app_pick(Nat.is_eq(i, x), cl, x, t, b, cfd.marks_app(x, t, b))

# The model's view, projected
# ---------------------------

def cfd.mlist(m: Maybe<&2, Cr.Claim>) -> List<&2, Cr.Claim>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      [x]

def cfd.prow(+i: Nat, v: Cron.View()) -> CronFileView.FRow:
  (st, r1) = v
  (n, r2) = r1
  (k, cl) = r2
  CronFileView.FJob{i, st, n, k}

def cfd.pcl(v: Cron.View()) -> List<&2, Cr.Claim>:
  (st, r1) = v
  (n, r2) = r1
  (k, cl) = r2
  cfd.mlist(cl)

def cfd.row_view(j: Cr.Job, +u: Nat) -> {CronFileView.row_of(j, u) == cfd.prow(CronFileView.id_of(j), Cron.view(j, u)) : CronFileView.FRow}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      {==}

def cfd.own_view(j: Cr.Job, +u: Nat) -> {cfd.own(j, u) == cfd.pcl(Cron.view(j, u)) : List<&2, Cr.Claim>}:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match cl:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Cr.Claim{o, w}:
              {==}

# The first job of id x has id x
def cfd.IdIs(m: Maybe<&2, Cr.Job>, +x: Nat) -> Type:
  match m:
    case None{}:
      Unit
    case Some{j}:
      {Nat.is_eq(CronFileView.id_of(j), x) == True{} : Bool}

def cfd.first_id_pick(b: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +x: Nat, eq: {Nat.is_eq(CronFileView.id_of(j), x) == b : Bool}, ih: cfd.IdIs(cfd.first(x, t), x)) -> cfd.IdIs(cfd.first.pick(b, j, cfd.first(x, t)), x):
  match b:
    case True{}:
      eq
    case False{}:
      ih

def cfd.first_id(+x: Nat, rs: List<&2, Cr.Rec>) -> cfd.IdIs(cfd.first(x, rs), x):
  match rs:
    case Nil{}:
      Unit{}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          cfd.first_id_pick(Nat.is_eq(CronFileView.id_of(j), x), j, t, x, {==}, cfd.first_id(x, t))
        case Cr.Raw{y}:
          cfd.first_id(x, t)
