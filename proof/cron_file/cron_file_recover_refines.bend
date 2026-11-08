# eukhe: the proof of LAW cron_file_recover_refines
# Job by job (the first job of id x): a cleared claim record names x
# exactly when that job's claim on record is cleared by its verdict (no
# two jobs share an id; the records this build cannot read are never
# cleared), so its answer is the one cron_recover_refines ties to the
# model's recovery; the claim records naming x are its claim unless
# cleared. The answers for the claim records this build cannot read keep
# them all.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ../cron/cron_recover_refines.bend as PRecoverRefines
import ./base/file.bend as LCfd
import ./base/logic.bend as LCfl

# Bools
# -----

def crv.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def crv.and_t(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def crv.or_f(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Cleared
# -------

def crv.mcleared(+p: Nat, +dead: List<&2, Nat>, m: Maybe<&2, Cr.Job>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{j}:
      Cron.cleared_of(p, dead, j)

def crv.or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def crv.cl_app(+x: Nat, a: List<&2, CF.Hold>, +b: List<&2, CF.Hold>) -> {CronFile.cleared_spec(x, List.append(&2, CF.Hold, a, b)) == Bool.or(CronFile.cleared_spec(x, a), CronFile.cleared_spec(x, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(Bool, CronFile.cleared_spec(x, List.append(&2, CF.Hold, t, b)), Bool.or(CronFile.cleared_spec(x, t), CronFile.cleared_spec(x, b)), crv.cl_app(x, t, b)) : {Bool.or(CronFile.cleared_spec.one(x, c), _) == Bool.or(Bool.or(CronFile.cleared_spec.one(x, c), CronFile.cleared_spec(x, t)), CronFile.cleared_spec(x, b)) : Bool}
      crv.or_assoc(CronFile.cleared_spec.one(x, c), CronFile.cleared_spec(x, t), CronFile.cleared_spec(x, b))

def crv.cl_unheld(+x: Nat, rd: List<&2, Nat>) -> {CronFile.cleared_spec(x, CronFileView.unheld(rd)) == False{} : Bool}:
  match rd:
    case Nil{}:
      {==}
    case y <> t:
      crv.cl_unheld(x, t)

def crv.cl_none_one(+i: Nat, cl: Maybe<&2, Cr.Claim>, +p: Nat, ru: List<&2, Nat>, +dead: List<&2, Nat>, +x: Nat, +rest: List<&2, CF.Hold>, ne: {Nat.is_eq(x, i) == False{} : Bool}, ih: {CronFile.cleared_spec(x, rest) == False{} : Bool}) -> {CronFile.cleared_spec(x, CronFileView.holds_one(i, cl, p, ru, dead, rest)) == False{} : Bool}:
  match cl:
    case None{}:
      ih
    case Some{c}:
      match c:
        case Cr.Claim{o, +w}:
          +cs = CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead))
          %Equal.sym(Bool, Nat.is_eq(x, i), False{}, ne) : {Bool.or(Bool.and(cs, _), CronFile.cleared_spec(x, rest)) == False{} : Bool}
          %Equal.sym(Bool, Bool.and(cs, False{}), False{}, crv.and_f(cs)) : {Bool.or(_, CronFile.cleared_spec(x, rest)) == False{} : Bool}
          ih

def crv.cl_none(+x: Nat, +p: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +h: {CronFileView.has_id(x, rs) == False{} : Bool}) -> {CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, rs)) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +hh}:
              +ne = LCfl.cfl.ne_comm(i, x, LCfd.cfd.has_head(Cr.Job{i, s, st, nx, k, cl, ru, ss, hh}, t, x, h))
              crv.cl_none_one(i, cl, p, ru, dead, x, CronFileView.holds_of(p, dead, t), ne, crv.cl_none(x, p, dead, t, LCfd.cfd.has_tail(Cr.Job{i, s, st, nx, k, cl, ru, ss, hh}, t, x, h)))
        case Cr.Raw{y}:
          crv.cl_none(x, p, dead, t, h)

def crv.cl_pick(b: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +dead: List<&2, Nat>, +x: Nat, +t: List<&2, Cr.Rec>, +eq: {Nat.is_eq(i, x) == b : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, t)) == crv.mcleared(p, dead, LCfd.cfd.first(x, t)) : Bool}) -> {CronFile.cleared_spec(x, CronFileView.holds_one(i, cl, p, ru, dead, CronFileView.holds_of(p, dead, t))) == crv.mcleared(p, dead, LCfd.cfd.first.pick(b, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, LCfd.cfd.first(x, t))) : Bool}:
  match b:
    case True{}:
      match cl:
        case None{}:
          crv.cl_none(x, p, dead, t, LCfd.cfd.has_move(i, x, t, LCfl.cfl.eq_of(i, x, eq), nt))
        case Some{c}:
          match c:
            case Cr.Claim{o, +w}:
              +cs = CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead))
              %Equal.sym(Bool, Nat.is_eq(x, i), True{}, Equal.trans(Bool, Nat.is_eq(x, i), Nat.is_eq(i, x), True{}, LCfl.cfl.eq_comm(x, i), eq)) : {Bool.or(Bool.and(cs, _), CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, t))) == cs : Bool}
              %Equal.sym(Bool, CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, t)), False{}, crv.cl_none(x, p, dead, t, LCfd.cfd.has_move(i, x, t, LCfl.cfl.eq_of(i, x, eq), nt))) : {Bool.or(Bool.and(cs, True{}), _) == cs : Bool}
              %Equal.sym(Bool, Bool.and(cs, True{}), cs, crv.and_t(cs)) : {Bool.or(_, False{}) == cs : Bool}
              crv.or_f(cs)
    case False{}:
      match cl:
        case None{}:
          ih
        case Some{c}:
          match c:
            case Cr.Claim{o, +w}:
              +cs = CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead))
              %Equal.sym(Bool, Nat.is_eq(x, i), False{}, Equal.trans(Bool, Nat.is_eq(x, i), Nat.is_eq(i, x), False{}, LCfl.cfl.eq_comm(x, i), eq)) : {Bool.or(Bool.and(cs, _), CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, t))) == crv.mcleared(p, dead, LCfd.cfd.first(x, t)) : Bool}
              %Equal.sym(Bool, Bool.and(cs, False{}), False{}, crv.and_f(cs)) : {Bool.or(_, CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, t))) == crv.mcleared(p, dead, LCfd.cfd.first(x, t)) : Bool}
              ih

# no two jobs share an id: a cleared claim record names x exactly when the
# first job of id x has its claim cleared
def crv.cl(+x: Nat, +p: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +d: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, rs)) == crv.mcleared(p, dead, LCfd.cfd.first(x, rs)) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +h}:
              crv.cl_pick(Nat.is_eq(i, x), i, s, st, nx, k, cl, ru, ss, h, p, dead, x, t, {==}, LCfd.cfd.distinct_head(Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, t, d), crv.cl(x, p, dead, t, LCfd.cfd.distinct_tail(Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, t, d)))
        case Cr.Raw{y}:
          crv.cl(x, p, dead, t, d)

def crv.cx(+x: Nat, +p: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, +rd: List<&2, Nat>, +d: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFile.cleared_spec(x, List.append(&2, CF.Hold, CronFileView.holds_of(p, dead, rs), CronFileView.unheld(rd))) == crv.mcleared(p, dead, LCfd.cfd.first(x, rs)) : Bool}:
  %Equal.sym(Bool, CronFile.cleared_spec(x, List.append(&2, CF.Hold, CronFileView.holds_of(p, dead, rs), CronFileView.unheld(rd))), Bool.or(CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, rs)), CronFile.cleared_spec(x, CronFileView.unheld(rd))), crv.cl_app(x, CronFileView.holds_of(p, dead, rs), CronFileView.unheld(rd))) : {_ == crv.mcleared(p, dead, LCfd.cfd.first(x, rs)) : Bool}
  %Equal.sym(Bool, CronFile.cleared_spec(x, CronFileView.unheld(rd)), False{}, crv.cl_unheld(x, rd)) : {Bool.or(CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, rs)), _) == crv.mcleared(p, dead, LCfd.cfd.first(x, rs)) : Bool}
  %Equal.sym(Bool, Bool.or(CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, rs)), False{}), CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, rs)), crv.or_f(CronFile.cleared_spec(x, CronFileView.holds_of(p, dead, rs)))) : {_ == crv.mcleared(p, dead, LCfd.cfd.first(x, rs)) : Bool}
  crv.cl(x, p, dead, rs, d)

# Rows
# ----

def crv.mrow(+x: Nat, m: Maybe<&2, Cr.Job>, +hs: List<&2, CF.Hold>, +u: Nat) -> Maybe<&2, CronFileView.FRow>:
  match m:
    case None{}:
      None{}
    case Some{+j}:
      Some{CronFileView.back_row(CronStore.recover_spec(Cron.fact_of(j, u), CronFile.cleared_spec(x, hs)), j, u)}

def crv.back_head(b: CS.Back, j: Cr.Job, +x: Nat, +u: Nat, +rest: List<&2, CronFileView.FRow>) -> {CronFileView.row_at(x, CronFileView.back_row(b, j, u) <> rest) == CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.back_row(b, j, u), CronFileView.row_at(x, rest)) : Maybe<&2, CronFileView.FRow>}:
  match b:
    case CS.Kept{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Interrupted{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

def crv.rows_pick(b: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +hs: List<&2, CF.Hold>, +u: Nat, +x: Nat, eq: {Nat.is_eq(CronFileView.id_of(j), x) == b : Bool}, ih: {CronFileView.row_at(x, CronFileView.recover_rows(t, CronFile.recover_js_spec(CronFileView.slots_of(t, u), hs), u)) == crv.mrow(x, LCfd.cfd.first(x, t), hs, u) : Maybe<&2, CronFileView.FRow>}) -> {CronFileView.row_at.pick(b, CronFileView.back_row(CronStore.recover_spec(Cron.fact_of(j, u), CronFile.cleared_spec(CronFileView.id_of(j), hs)), j, u), CronFileView.row_at(x, CronFileView.recover_rows(t, CronFile.recover_js_spec(CronFileView.slots_of(t, u), hs), u))) == crv.mrow(x, LCfd.cfd.first.pick(b, j, LCfd.cfd.first(x, t)), hs, u) : Maybe<&2, CronFileView.FRow>}:
  match b:
    case True{}:
      %LCfl.cfl.eq_of(CronFileView.id_of(j), x, eq) : {Some{CronFileView.back_row(CronStore.recover_spec(Cron.fact_of(j, u), CronFile.cleared_spec(CronFileView.id_of(j), hs)), j, u)} == Some{CronFileView.back_row(CronStore.recover_spec(Cron.fact_of(j, u), CronFile.cleared_spec(_, hs)), j, u)} : Maybe<&2, CronFileView.FRow>}
      {==}
    case False{}:
      ih

def crv.rows(+x: Nat, rs: List<&2, Cr.Rec>, +hs: List<&2, CF.Hold>, +u: Nat) -> {CronFileView.row_at(x, CronFileView.recover_rows(rs, CronFile.recover_js_spec(CronFileView.slots_of(rs, u), hs), u)) == crv.mrow(x, LCfd.cfd.first(x, rs), hs, u) : Maybe<&2, CronFileView.FRow>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          +a = CronStore.recover_spec(Cron.fact_of(j, u), CronFile.cleared_spec(CronFileView.id_of(j), hs))
          +rest = CronFileView.recover_rows(t, CronFile.recover_js_spec(CronFileView.slots_of(t, u), hs), u)
          %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.back_row(a, j, u) <> rest), CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.back_row(a, j, u), CronFileView.row_at(x, rest)), crv.back_head(a, j, x, u, rest)) : {_ == crv.mrow(x, LCfd.cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, LCfd.cfd.first(x, t)), hs, u) : Maybe<&2, CronFileView.FRow>}
          crv.rows_pick(Nat.is_eq(CronFileView.id_of(j), x), j, t, hs, u, x, {==}, crv.rows(x, t, hs, u))
        case Cr.Raw{y}:
          crv.rows(x, t, hs, u)

def crv.raw_back(b: CS.Back, j: Cr.Job, +u: Nat, rest: List<&2, CronFileView.FRow>) -> {CronFileView.raw_rows(CronFileView.back_row(b, j, u) <> rest) == CronFileView.raw_rows(rest) : List<&2, Nat>}:
  match b:
    case CS.Kept{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Interrupted{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

def crv.raws(rs: List<&2, Cr.Rec>, bs: List<&2, CS.Back>, +u: Nat) -> {CronFileView.raw_rows(CronFileView.recover_rows(rs, bs, u)) == CronFileView.raw_rows(CronFileView.rows_of(rs, u)) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          match bs:
            case Nil{}:
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.recover_rows(t, Nil{}, u)), CronFileView.raw_rows(CronFileView.recover_rows(t, Nil{}, u)), LCfd.cfd.raw_head(j, u, CronFileView.recover_rows(t, Nil{}, u))) : {_ == CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)) : List<&2, Nat>}
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.raw_rows(CronFileView.rows_of(t, u)), LCfd.cfd.raw_head(j, u, CronFileView.rows_of(t, u))) : {CronFileView.raw_rows(CronFileView.recover_rows(t, Nil{}, u)) == _ : List<&2, Nat>}
              crv.raws(t, Nil{}, u)
            case +b <> +rest:
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.back_row(b, j, u) <> CronFileView.recover_rows(t, rest, u)), CronFileView.raw_rows(CronFileView.recover_rows(t, rest, u)), crv.raw_back(b, j, u, CronFileView.recover_rows(t, rest, u))) : {_ == CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)) : List<&2, Nat>}
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.raw_rows(CronFileView.rows_of(t, u)), LCfd.cfd.raw_head(j, u, CronFileView.rows_of(t, u))) : {CronFileView.raw_rows(CronFileView.recover_rows(t, rest, u)) == _ : List<&2, Nat>}
              crv.raws(t, rest, u)
        case Cr.Raw{+y}:
          %crv.raws(t, bs, u) : {y <> CronFileView.raw_rows(CronFileView.recover_rows(t, bs, u)) == y <> _ : List<&2, Nat>}
          {==}

# The claim records kept
# ----------------------

def crv.kept_j(+p: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +u: Nat) -> List<&2, Cr.Claim>:
  LCfd.cfd.mlist(Cron.claim_after(Cron.cleared_of(p, dead, j), Cron.scale_claim(Cr.Job.claim(j), u)))

def crv.mkept(+p: Nat, +dead: List<&2, Nat>, m: Maybe<&2, Cr.Job>, +u: Nat) -> List<&2, Cr.Claim>:
  match m:
    case None{}:
      Nil{}
    case Some{j}:
      crv.kept_j(p, dead, j, u)

def crv.keep_false(k: Bool, +i: Nat, +c: Cr.Claim, +x: Nat, +rest: List<&2, CronFileView.FClaim>, ne: {Nat.is_eq(i, x) == False{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.keep.pick(k, CronFileView.FClaim{i, c}, rest)) == CronFileView.marks_at(x, rest) : List<&2, Cr.Claim>}:
  match k:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), False{}, ne) : {CronFileView.marks_at.pick(_, c, CronFileView.marks_at(x, rest)) == CronFileView.marks_at(x, rest) : List<&2, Cr.Claim>}
      {==}
    case False{}:
      {==}

def crv.keep_true(cs: Bool, +i: Nat, +c: Cr.Claim, +x: Nat, +rest: List<&2, CronFileView.FClaim>, eq: {Nat.is_eq(i, x) == True{} : Bool}, nil: {CronFileView.marks_at(x, rest) == Nil{} : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.keep.pick(Bool.not(cs), CronFileView.FClaim{i, c}, rest)) == LCfd.cfd.mlist(Cron.claim_after(cs, Some{c})) : List<&2, Cr.Claim>}:
  match cs:
    case True{}:
      nil
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, eq) : {CronFileView.marks_at.pick(_, c, CronFileView.marks_at(x, rest)) == [c] : List<&2, Cr.Claim>}
      %nil : {c <> CronFileView.marks_at(x, rest) == c <> _ : List<&2, Cr.Claim>}
      {==}

def crv.marks_none_c(ks: List<&2, Bool>, +i: Nat, +o: Nat, +w: Nat, +x: Nat, +t: List<&2, Cr.Rec>, +u: Nat, ne: {Nat.is_eq(i, x) == False{} : Bool}, -ht: {CronFileView.has_id(x, t) == False{} : Bool}, ih: @q: List<&2, Bool> -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), q)) == Nil{} : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}} <> CronFileView.marks_of(t, u), ks)) == Nil{} : List<&2, Cr.Claim>}:
  match ks:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), False{}, ne) : {CronFileView.marks_at.pick(_, Cr.Claim{Nat.mul(o, u), w}, CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), Nil{}))) == Nil{} : List<&2, Cr.Claim>}
      ih(Nil{})
    case +kk <> +rest:
      %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.keep.pick(kk, CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}}, CronFileView.select_marks(CronFileView.marks_of(t, u), rest))), CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), rest)), crv.keep_false(kk, i, Cr.Claim{Nat.mul(o, u), w}, x, CronFileView.select_marks(CronFileView.marks_of(t, u), rest), ne)) : {_ == Nil{} : List<&2, Cr.Claim>}
      ih(rest)

# no job of id x: no kept claim record names x
def crv.marks_none(+x: Nat, rs: List<&2, Cr.Rec>, ks: List<&2, Bool>, +u: Nat, +h: {CronFileView.has_id(x, rs) == False{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(rs, u), ks)) == Nil{} : List<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, cl, +ru, +ss, +hh}:
              match cl:
                case None{}:
                  crv.marks_none(x, t, ks, u, LCfd.cfd.has_tail(Cr.Job{i, s, st, nx, k, None{}, ru, ss, hh}, t, x, h))
                case Some{c}:
                  match c:
                    case Cr.Claim{+o, +w}:
                      +ne = LCfd.cfd.has_head(Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, hh}, t, x, h)
                      +ht = LCfd.cfd.has_tail(Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, hh}, t, x, h)
                      crv.marks_none_c(ks, i, o, w, x, t, u, ne, ht, (q => crv.marks_none(x, t, q, u, ht)))
        case Cr.Raw{y}:
          crv.marks_none(x, t, ks, u, h)

def crv.marks_nil(+x: Nat, xs: List<&2, Bool>, +u: Nat) -> {CronFileView.marks_at(x, CronFileView.select_marks(Nil{}, xs)) == Nil{} : List<&2, Cr.Claim>}:
  match xs:
    case Nil{}:
      {==}
    case y <> t:
      {==}

def crv.marks_some(b: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +o: Nat, +w: Nat, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +dead: List<&2, Nat>, +x: Nat, +t: List<&2, Cr.Rec>, +rest: List<&2, Bool>, +u: Nat, +eq: {Nat.is_eq(i, x) == b : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), rest)) == crv.mkept(p, dead, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.keep.pick(Bool.not(CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead))), CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}}, CronFileView.select_marks(CronFileView.marks_of(t, u), rest))) == crv.mkept(p, dead, LCfd.cfd.first.pick(b, Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h}, LCfd.cfd.first(x, t)), u) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      crv.keep_true(CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead)), i, Cr.Claim{Nat.mul(o, u), w}, x, CronFileView.select_marks(CronFileView.marks_of(t, u), rest), eq, crv.marks_none(x, t, rest, u, LCfd.cfd.has_move(i, x, t, LCfl.cfl.eq_of(i, x, eq), nt)))
    case False{}:
      %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.keep.pick(Bool.not(CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead))), CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}}, CronFileView.select_marks(CronFileView.marks_of(t, u), rest))), CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), rest)), crv.keep_false(Bool.not(CronStore.clear_spec(Cron.who_of.pick(Nat.is_eq(w, p), p, w, ru, dead))), i, Cr.Claim{Nat.mul(o, u), w}, x, CronFileView.select_marks(CronFileView.marks_of(t, u), rest), eq)) : {_ == crv.mkept(p, dead, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}
      ih

def crv.marks_nocl(b: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +dead: List<&2, Nat>, +x: Nat, +t: List<&2, Cr.Rec>, +ks: List<&2, Bool>, +u: Nat, +eq: {Nat.is_eq(i, x) == b : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks)) == crv.mkept(p, dead, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks)) == crv.mkept(p, dead, LCfd.cfd.first.pick(b, Cr.Job{i, s, st, nx, k, None{}, ru, ss, h}, LCfd.cfd.first(x, t)), u) : List<&2, Cr.Claim>}:
  match b:
    case True{}:
      crv.marks_none(x, t, ks, u, LCfd.cfd.has_move(i, x, t, LCfl.cfl.eq_of(i, x, eq), nt))
    case False{}:
      ih

# no two jobs share an id: the claim records naming x a recovery keeps are
# the first job of id x's claim, unless its verdict cleared it
def crv.marks(+x: Nat, +p: Nat, +dead: List<&2, Nat>, rs: List<&2, Cr.Rec>, +xs: List<&2, Bool>, +u: Nat, +d: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(rs, u), List.append(&2, Bool, CronFile.keeps_spec(CronFileView.holds_of(p, dead, rs)), xs))) == crv.mkept(p, dead, LCfd.cfd.first(x, rs), u) : List<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      crv.marks_nil(x, xs, u)
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, cl, +ru, +ss, +h}:
              match cl:
                case None{}:
                  +jj = {Cr.Job{i, s, st, nx, k, None{}, ru, ss, h} : Cr.Job}
                  crv.marks_nocl(Nat.is_eq(i, x), i, s, st, nx, k, ru, ss, h, p, dead, x, t, List.append(&2, Bool, CronFile.keeps_spec(CronFileView.holds_of(p, dead, t)), xs), u, {==}, LCfd.cfd.distinct_head(jj, t, d), crv.marks(x, p, dead, t, xs, u, LCfd.cfd.distinct_tail(jj, t, d)))
                case Some{c}:
                  match c:
                    case Cr.Claim{+o, +w}:
                      +jj = {Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h} : Cr.Job}
                      crv.marks_some(Nat.is_eq(i, x), i, s, st, nx, k, o, w, ru, ss, h, p, dead, x, t, List.append(&2, Bool, CronFile.keeps_spec(CronFileView.holds_of(p, dead, t)), xs), u, {==}, LCfd.cfd.distinct_head(jj, t, d), crv.marks(x, p, dead, t, xs, u, LCfd.cfd.distinct_tail(jj, t, d)))
        case Cr.Raw{y}:
          crv.marks(x, p, dead, t, xs, u, d)

# The claim records this build cannot read
# ----------------------------------------

def crv.after(rs: List<&2, Cr.Rec>, +p: Nat, +dead: List<&2, Nat>, +u: Nat, +xs: List<&2, Bool>) -> {CronFileView.after_marks(CronFileView.marks_of(rs, u), List.append(&2, Bool, CronFile.keeps_spec(CronFileView.holds_of(p, dead, rs)), xs)) == xs : List<&2, Bool>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{i, s, st, nx, k, cl, ru, ss, h}:
              match cl:
                case None{}:
                  crv.after(t, p, dead, u, xs)
                case Some{c}:
                  match c:
                    case Cr.Claim{o, w}:
                      crv.after(t, p, dead, u, xs)
        case Cr.Raw{y}:
          crv.after(t, p, dead, u, xs)

def crv.keeps_app(a: List<&2, CF.Hold>, +b: List<&2, CF.Hold>) -> {CronFile.keeps_spec(List.append(&2, CF.Hold, a, b)) == List.append(&2, Bool, CronFile.keeps_spec(a), CronFile.keeps_spec(b)) : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(List<&2, Bool>, CronFile.keeps_spec(List.append(&2, CF.Hold, t, b)), List.append(&2, Bool, CronFile.keeps_spec(t), CronFile.keeps_spec(b)), crv.keeps_app(t, b)) : {CronFile.keep_spec(c) <> _ == CronFile.keep_spec(c) <> List.append(&2, Bool, CronFile.keeps_spec(t), CronFile.keeps_spec(b)) : List<&2, Bool>}
      {==}

def crv.raws_keep(rd: List<&2, Nat>) -> {CronFileView.select_raws(rd, CronFile.keeps_spec(CronFileView.unheld(rd))) == rd : List<&2, Nat>}:
  match rd:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(List<&2, Nat>, CronFileView.select_raws(t, CronFile.keeps_spec(CronFileView.unheld(t))), t, crv.raws_keep(t)) : {y <> _ == y <> t : List<&2, Nat>}
      {==}

# One job, against cron_recover_refines
# -------------------------------------

def crv.row_back(b: CS.Back, +cl: Bool, j: Cr.Job, +u: Nat) -> {CronFileView.back_row(b, j, u) == LCfd.cfd.prow(CronFileView.id_of(j), Cron.back_view(b, cl, j, u)) : CronFileView.FRow}:
  match b:
    case CS.Kept{}:
      match j:
        case Cr.Job{i, s, st, nx, k, c, rs, ss, h}:
          {==}
    case CS.Interrupted{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, c, rs, ss, h}:
          {==}

def crv.kept_back(b: CS.Back, +p: Nat, +dead: List<&2, Nat>, j: Cr.Job, +u: Nat) -> {crv.kept_j(p, dead, j, u) == LCfd.cfd.pcl(Cron.back_view(b, Cron.cleared_of(p, dead, j), j, u)) : List<&2, Cr.Claim>}:
  match b:
    case CS.Kept{}:
      match j:
        case Cr.Job{i, s, st, nx, k, c, rs, ss, h}:
          {==}
    case CS.Interrupted{st2, m}:
      match j:
        case Cr.Job{i, s, st, nx, k, c, rs, ss, h}:
          {==}

def crv.some(+v: Nat, +p: Nat, +dead: List<&2, Nat>, +j: Cr.Job, +r3: List<&2, Nat>, +rd: List<&2, Nat>, +alive: {Cr.has(p, dead) == False{} : Bool}) -> {(Some{CronFileView.back_row(CronStore.recover_spec(Cron.fact_of(j, 1n+v), Cron.cleared_of(p, dead, j)), j, 1n+v)}, (crv.kept_j(p, dead, j, 1n+v), (r3, rd))) == (Some{CronFileView.row_of(Cr.recover(p, dead, j), 1n+v)}, (LCfd.cfd.own(Cr.recover(p, dead, j), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  +u = {1n+v : Nat}
  +cl = Cron.cleared_of(p, dead, j)
  +b = CronStore.recover_spec(Cron.fact_of(j, u), cl)
  -bv = Cron.back_view(b, cl, j, u)
  -vv = Cron.view(Cr.recover(p, dead, j), u)
  %Equal.sym(CronFileView.FRow, CronFileView.back_row(b, j, u), LCfd.cfd.prow(CronFileView.id_of(j), bv), crv.row_back(b, cl, j, u)) : {(Some{_}, (crv.kept_j(p, dead, j, u), (r3, rd))) == (Some{CronFileView.row_of(Cr.recover(p, dead, j), u)}, (LCfd.cfd.own(Cr.recover(p, dead, j), u), (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, crv.kept_j(p, dead, j, u), LCfd.cfd.pcl(bv), crv.kept_back(b, p, dead, j, u)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), bv)}, (_, (r3, rd))) == (Some{CronFileView.row_of(Cr.recover(p, dead, j), u)}, (LCfd.cfd.own(Cr.recover(p, dead, j), u), (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(CronFileView.FRow, CronFileView.row_of(Cr.recover(p, dead, j), u), LCfd.cfd.prow(CronFileView.id_of(Cr.recover(p, dead, j)), vv), LCfd.cfd.row_view(Cr.recover(p, dead, j), u)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), bv)}, (LCfd.cfd.pcl(bv), (r3, rd))) == (Some{_}, (LCfd.cfd.own(Cr.recover(p, dead, j), u), (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, LCfd.cfd.own(Cr.recover(p, dead, j), u), LCfd.cfd.pcl(vv), LCfd.cfd.own_view(Cr.recover(p, dead, j), u)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), bv)}, (LCfd.cfd.pcl(bv), (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(Cr.recover(p, dead, j)), vv)}, (_, (r3, rd))) : CronFileView.Obs()}
  %Equal.sym(Nat, CronFileView.id_of(Cr.job(Cr.Recover{p}, 0n, dead, j)), CronFileView.id_of(j), LCfd.cfd.id_job(Cr.Recover{p}, 0n, dead, j)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), bv)}, (LCfd.cfd.pcl(bv), (r3, rd))) == (Some{LCfd.cfd.prow(_, vv)}, (LCfd.cfd.pcl(vv), (r3, rd))) : CronFileView.Obs()}
  %Cron.cron_recover_refines(v, p, dead, j, alive) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), bv)}, (LCfd.cfd.pcl(bv), (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(j), _)}, (LCfd.cfd.pcl(_), (r3, rd))) : CronFileView.Obs()}
  {==}

def crv.final(+v: Nat, +p: Nat, +c: Nat, +x: Nat, +dead: List<&2, Nat>, m: Maybe<&2, Cr.Job>, +r3: List<&2, Nat>, +rd: List<&2, Nat>, +hs: List<&2, CF.Hold>, cx: {CronFile.cleared_spec(x, hs) == crv.mcleared(p, dead, m) : Bool}, +alive: {Cr.has(p, dead) == False{} : Bool}) -> {(crv.mrow(x, m, hs, 1n+v), (crv.mkept(p, dead, m, 1n+v), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Recover{p}, c, dead, m), 1n+v), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Recover{p}, c, dead, m), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      %Equal.sym(Bool, CronFile.cleared_spec(x, hs), Cron.cleared_of(p, dead, j), cx) : {(Some{CronFileView.back_row(CronStore.recover_spec(Cron.fact_of(j, 1n+v), _), j, 1n+v)}, (crv.kept_j(p, dead, j, 1n+v), (r3, rd))) == (Some{CronFileView.row_of(Cr.recover(p, dead, j), 1n+v)}, (LCfd.cfd.own(Cr.recover(p, dead, j), 1n+v), (r3, rd))) : CronFileView.Obs()}
      crv.some(v, p, dead, j, r3, rd, alive)

def CronFileView.cron_file_recover_refines(v, p, c, x, dead, rs, rd, ok0, alive0):
  +ok = ok0
  +alive = alive0
  +u = {1n+v : Nat}
  +hs = List.append(&2, CF.Hold, CronFileView.holds_of(p, dead, rs), CronFileView.unheld(rd))
  +kh = CronFile.keeps_spec(CronFileView.holds_of(p, dead, rs))
  +ku = CronFile.keeps_spec(CronFileView.unheld(rd))
  +ms = CronFileView.marks_of(rs, u)
  +bs = CronFile.recover_js_spec(CronFileView.slots_of(rs, u), hs)
  +rr = Cr.recs(Cr.Recover{p}, c, dead, rs)
  +f = LCfd.cfd.first(x, rs)
  +r3 = CronFileView.raw_rows(CronFileView.rows_of(rs, u))
  -mr = crv.mrow(x, f, hs, u)
  -mk = crv.mkept(p, dead, f, u)
  +drr = Equal.trans(Bool, CronFileView.distinct(rr), CronFileView.distinct(rs), True{}, LCfd.cfd.distinct_recs(Cr.Recover{p}, c, dead, rs), ok)
  %Equal.sym(List<&2, Bool>, CronFile.keeps_spec(hs), List.append(&2, Bool, kh, ku), crv.keeps_app(CronFileView.holds_of(p, dead, rs), CronFileView.unheld(rd))) : {(CronFileView.row_at(x, CronFileView.recover_rows(rs, bs, u)), (CronFileView.marks_at(x, CronFileView.select_marks(ms, _)), (CronFileView.raw_rows(CronFileView.recover_rows(rs, bs, u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, _))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.recover_rows(rs, bs, u)), mr, crv.rows(x, rs, hs, u)) : {(_, (CronFileView.marks_at(x, CronFileView.select_marks(ms, List.append(&2, Bool, kh, ku))), (CronFileView.raw_rows(CronFileView.recover_rows(rs, bs, u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, List.append(&2, Bool, kh, ku)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.select_marks(ms, List.append(&2, Bool, kh, ku))), mk, crv.marks(x, p, dead, rs, ku, u, ok)) : {(mr, (_, (CronFileView.raw_rows(CronFileView.recover_rows(rs, bs, u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, List.append(&2, Bool, kh, ku)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.recover_rows(rs, bs, u)), r3, crv.raws(rs, bs, u)) : {(mr, (mk, (_, CronFileView.select_raws(rd, CronFileView.after_marks(ms, List.append(&2, Bool, kh, ku)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Bool>, CronFileView.after_marks(ms, List.append(&2, Bool, kh, ku)), ku, crv.after(rs, p, dead, u, ku)) : {(mr, (mk, (r3, CronFileView.select_raws(rd, _)))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.select_raws(rd, ku), rd, crv.raws_keep(rd)) : {(mr, (mk, (r3, _))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.rows_of(rr, u)), LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), LCfd.cfd.rows_at(x, rr, u)) : {(mr, (mk, (r3, rd))) == (_, (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), LCfd.cfd.mclaims(LCfd.cfd.first(x, rr), u), LCfd.cfd.marks_at(x, rr, u, drr)) : {(mr, (mk, (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), (_, (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.rows_of(rr, u)), r3, LCfd.cfd.raws_recs(Cr.Recover{p}, c, dead, rs, u)) : {(mr, (mk, (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), (LCfd.cfd.mclaims(LCfd.cfd.first(x, rr), u), (_, rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, Cr.Job>, LCfd.cfd.first(x, rr), LCfd.cfd.mapj(Cr.Recover{p}, c, dead, f), LCfd.cfd.first_recs(Cr.Recover{p}, c, dead, rs, x)) : {(mr, (mk, (r3, rd))) == (LCfd.cfd.mrow(_, u), (LCfd.cfd.mclaims(_, u), (r3, rd))) : CronFileView.Obs()}
  crv.final(v, p, c, x, dead, f, r3, rd, hs, crv.cx(x, p, dead, rs, rd, ok), alive)
