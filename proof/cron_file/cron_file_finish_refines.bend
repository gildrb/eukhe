# eukhe: the proof of LAW cron_file_finish_refines
# The dispatch's claim record is the claim of job ji that p holds and
# runs; no two jobs share an id, so it is at most one record, on the
# first job of id ji, and the key the finish step reads is ji exactly when
# that job is p's and p runs it (`cfn.hit`). Job by job (the first job of
# id x): when x is ji and the job is p's and run, its row is the answer
# cron_finish_refines ties to the model's finish step and its claim record
# goes; otherwise nothing of it changes, and the model's finish step of it
# changes nothing either (`cfn.noop`).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron.bend as Cron
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ../cron/cron_finish_refines.bend as PFinishRefines
import ./base/file.bend as LCfd
import ./base/logic.bend as LCfl
import ./cron_file_recover_refines.bend as LCrv
import ../cron/base/cron.bend as LACron

# Whose the claim is
# ------------------

# the job's claim on record is p's and p runs the job
def cfn.owned(+p: Nat, j: Cr.Job) -> Bool:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, ru, ss, h}:
      match cl:
        case None{}:
          False{}
        case Some{c}:
          match c:
            case Cr.Claim{o, w}:
              Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))

def cfn.hk(b: Bool, +ji: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{ji}
    case False{}:
      None{}

def cfn.mhit(+p: Nat, +ji: Nat, m: Maybe<&2, Cr.Job>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      cfn.hk(cfn.owned(p, j), ji)

def cfn.hit_unpinned(rd: List<&2, Nat>) -> {CronFile.hit_spec(CronFileView.unpinned(rd)) == None{} : Maybe<&2, Nat>}:
  match rd:
    case Nil{}:
      {==}
    case y <> t:
      cfn.hit_unpinned(t)

def cfn.hit_app(a: List<&2, CF.Pin>, rd: List<&2, Nat>) -> {CronFile.hit_spec(List.append(&2, CF.Pin, a, CronFileView.unpinned(rd))) == CronFile.hit_spec(a) : Maybe<&2, Nat>}:
  match a:
    case Nil{}:
      cfn.hit_unpinned(rd)
    case c <> +t:
      match c:
        case CF.Pinned{m, h}:
          %Equal.sym(Maybe<&2, Nat>, CronFile.hit_spec(List.append(&2, CF.Pin, t, CronFileView.unpinned(rd))), CronFile.hit_spec(t), cfn.hit_app(t, rd)) : {CronFile.hit_spec.pin(h, m, _) == CronFile.hit_spec.pin(h, m, CronFile.hit_spec(t)) : Maybe<&2, Nat>}
          {==}
        case CF.Unpinned{}:
          cfn.hit_app(t, rd)

def cfn.hit_none(+p: Nat, +ji: Nat, rs: List<&2, Cr.Rec>, +h: {CronFileView.has_id(ji, rs) == False{} : Bool}) -> {CronFile.hit_spec(CronFileView.pins_of(p, ji, rs)) == None{} : Maybe<&2, Nat>}:
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
                  cfn.hit_none(p, ji, t, LCfd.cfd.has_tail(Cr.Job{i, s, st, nx, k, None{}, ru, ss, hh}, t, ji, h))
                case Some{c}:
                  match c:
                    case Cr.Claim{+o, +w}:
                      +jj = {Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, hh} : Cr.Job}
                      %Equal.sym(Bool, Nat.is_eq(i, ji), False{}, LCfd.cfd.has_head(jj, t, ji, h)) : {CronFile.hit_spec.pin(Bool.and(_, Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), Some{i}, CronFile.hit_spec(CronFileView.pins_of(p, ji, t))) == None{} : Maybe<&2, Nat>}
                      cfn.hit_none(p, ji, t, LCfd.cfd.has_tail(jj, t, ji, h))
        case Cr.Raw{y}:
          cfn.hit_none(p, ji, t, h)

def cfn.hit_ow(ow: Bool, +i: Nat, +ji: Nat, +rest: Maybe<&2, Nat>, ij: {i == ji : Nat}, rn: {rest == None{} : Maybe<&2, Nat>}) -> {CronFile.hit_spec.pin(ow, Some{i}, rest) == cfn.hk(ow, ji) : Maybe<&2, Nat>}:
  match ow:
    case True{}:
      %ij : {Some{i} == Some{_} : Maybe<&2, Nat>}
      {==}
    case False{}:
      rn

def cfn.hit_pick(b: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +cl: Maybe<&2, Cr.Claim>, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +ji: Nat, +t: List<&2, Cr.Rec>, +eq: {Nat.is_eq(i, ji) == b : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFile.hit_spec(CronFileView.pins_of(p, ji, t)) == cfn.mhit(p, ji, LCfd.cfd.first(ji, t)) : Maybe<&2, Nat>}) -> {CronFile.hit_spec(CronFileView.pins_one(i, cl, p, ji, ru, CronFileView.pins_of(p, ji, t))) == cfn.mhit(p, ji, LCfd.cfd.first.pick(b, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, LCfd.cfd.first(ji, t))) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      match cl:
        case None{}:
          cfn.hit_none(p, ji, t, LCfd.cfd.has_move(i, ji, t, LCfl.cfl.eq_of(i, ji, eq), nt))
        case Some{c}:
          match c:
            case Cr.Claim{o, +w}:
              +ij = LCfl.cfl.eq_of(i, ji, eq)
              +none = cfn.hit_none(p, ji, t, LCfd.cfd.has_move(i, ji, t, ij, nt))
              %Equal.sym(Bool, Nat.is_eq(i, ji), True{}, eq) : {CronFile.hit_spec.pin(Bool.and(_, Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), Some{i}, CronFile.hit_spec(CronFileView.pins_of(p, ji, t))) == cfn.hk(Bool.and(Nat.is_eq(w, p), Cr.has(p, ru)), ji) : Maybe<&2, Nat>}
              cfn.hit_ow(Bool.and(Nat.is_eq(w, p), Cr.has(p, ru)), i, ji, CronFile.hit_spec(CronFileView.pins_of(p, ji, t)), ij, none)
    case False{}:
      match cl:
        case None{}:
          ih
        case Some{c}:
          match c:
            case Cr.Claim{o, +w}:
              %Equal.sym(Bool, Nat.is_eq(i, ji), False{}, eq) : {CronFile.hit_spec.pin(Bool.and(_, Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), Some{i}, CronFile.hit_spec(CronFileView.pins_of(p, ji, t))) == cfn.mhit(p, ji, LCfd.cfd.first(ji, t)) : Maybe<&2, Nat>}
              ih

# no two jobs share an id: the key the finish step reads is ji exactly when
# the first job of id ji is p's and p runs it
def cfn.hit(+p: Nat, +ji: Nat, rs: List<&2, Cr.Rec>, +d: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFile.hit_spec(CronFileView.pins_of(p, ji, rs)) == cfn.mhit(p, ji, LCfd.cfd.first(ji, rs)) : Maybe<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +h}:
              +jj = {Cr.Job{i, s, st, nx, k, cl, ru, ss, h} : Cr.Job}
              cfn.hit_pick(Nat.is_eq(i, ji), i, s, st, nx, k, cl, ru, ss, h, p, ji, t, {==}, LCfd.cfd.distinct_head(jj, t, d), cfn.hit(p, ji, t, LCfd.cfd.distinct_tail(jj, t, d)))
        case Cr.Raw{y}:
          cfn.hit(p, ji, t, d)

# Rows
# ----

def cfn.fin_of(g: Bool, +j: Cr.Job, +u: Nat, +r: Bool, +b: Bool, +n: Nat) -> CS.Fin:
  match g:
    case True{}:
      CronStore.finish_spec(u, Cron.fact_of(j, u), r, b, n)
    case False{}:
      CS.Untouched{}

def cfn.mrow(+x: Nat, +ks: Maybe<&2, Nat>, m: Maybe<&2, Cr.Job>, +u: Nat, +r: Bool, +b: Bool, +n: Nat) -> Maybe<&2, CronFileView.FRow>:
  match m:
    case None{}:
      None{}
    case Some{+j}:
      Some{CronFileView.fin_row(cfn.fin_of(CronFile.names_spec(x, ks), j, u, r, b, n), j, u)}

def cfn.fin_head(f: CS.Fin, j: Cr.Job, +x: Nat, +u: Nat, +rest: List<&2, CronFileView.FRow>) -> {CronFileView.row_at(x, CronFileView.fin_row(f, j, u) <> rest) == CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.fin_row(f, j, u), CronFileView.row_at(x, rest)) : Maybe<&2, CronFileView.FRow>}:
  match f:
    case CS.Untouched{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Ran{st2, nn, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Skipped{st2, nn, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

def cfn.untouched_rows(t: List<&2, Cr.Rec>, +u: Nat) -> {CronFileView.finish_rows(t, CronFile.untouched_spec(CronFileView.slots_of(t, u)), u) == CronFileView.rows_of(t, u) : List<&2, CronFileView.FRow>}:
  match t:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Cr.Known{+j}:
          %Equal.sym(List<&2, CronFileView.FRow>, CronFileView.finish_rows(rest, CronFile.untouched_spec(CronFileView.slots_of(rest, u)), u), CronFileView.rows_of(rest, u), cfn.untouched_rows(rest, u)) : {CronFileView.row_of(j, u) <> _ == CronFileView.row_of(j, u) <> CronFileView.rows_of(rest, u) : List<&2, CronFileView.FRow>}
          {==}
        case Cr.Raw{+y}:
          %Equal.sym(List<&2, CronFileView.FRow>, CronFileView.finish_rows(rest, CronFile.untouched_spec(CronFileView.slots_of(rest, u)), u), CronFileView.rows_of(rest, u), cfn.untouched_rows(rest, u)) : {CronFileView.FRaw{y} <> _ == CronFileView.FRaw{y} <> CronFileView.rows_of(rest, u) : List<&2, CronFileView.FRow>}
          {==}

def cfn.names_away(k: Maybe<&2, Nat>, +i: Nat, +x: Nat, g: {CronFile.names_spec(i, k) == True{} : Bool}, ne: {Nat.is_eq(i, x) == False{} : Bool}) -> {CronFile.names_spec(x, k) == False{} : Bool}:
  match k:
    case None{}:
      LCfl.cfl.absurdF({False{} == False{} : Bool}, g)
    case Some{+y}:
      +iy = LCfl.cfl.eq_of(i, y, g)
      %iy : {Nat.is_eq(x, _) == False{} : Bool}
      LCfl.cfl.ne_comm(i, x, ne)

def cfn.rows_off(+x: Nat, +ks: Maybe<&2, Nat>, m: Maybe<&2, Cr.Job>, +u: Nat, +r: Bool, +b: Bool, +n: Nat, off: {CronFile.names_spec(x, ks) == False{} : Bool}) -> {LCfd.cfd.mrow(m, u) == cfn.mrow(x, ks, m, u, r, b, n) : Maybe<&2, CronFileView.FRow>}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      %Equal.sym(Bool, CronFile.names_spec(x, ks), False{}, off) : {Some{CronFileView.row_of(j, u)} == Some{CronFileView.fin_row(cfn.fin_of(_, j, u, r, b, n), j, u)} : Maybe<&2, CronFileView.FRow>}
      {==}

def cfn.rows_t(bb: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +ks: Maybe<&2, Nat>, +u: Nat, +r: Bool, +b: Bool, +n: Nat, +x: Nat, +eqg: {CronFile.names_spec(CronFileView.id_of(j), ks) == True{} : Bool}, eq: {Nat.is_eq(CronFileView.id_of(j), x) == bb : Bool}) -> {CronFileView.row_at.pick(bb, CronFileView.fin_row(CronStore.finish_spec(u, Cron.fact_of(j, u), r, b, n), j, u), LCfd.cfd.mrow(LCfd.cfd.first(x, t), u)) == cfn.mrow(x, ks, LCfd.cfd.first.pick(bb, j, LCfd.cfd.first(x, t)), u, r, b, n) : Maybe<&2, CronFileView.FRow>}:
  match bb:
    case True{}:
      %LCfl.cfl.eq_of(CronFileView.id_of(j), x, eq) : {Some{CronFileView.fin_row(CronStore.finish_spec(u, Cron.fact_of(j, u), r, b, n), j, u)} == Some{CronFileView.fin_row(cfn.fin_of(CronFile.names_spec(_, ks), j, u, r, b, n), j, u)} : Maybe<&2, CronFileView.FRow>}
      %Equal.sym(Bool, CronFile.names_spec(CronFileView.id_of(j), ks), True{}, eqg) : {Some{CronFileView.fin_row(CronStore.finish_spec(u, Cron.fact_of(j, u), r, b, n), j, u)} == Some{CronFileView.fin_row(cfn.fin_of(_, j, u, r, b, n), j, u)} : Maybe<&2, CronFileView.FRow>}
      {==}
    case False{}:
      cfn.rows_off(x, ks, LCfd.cfd.first(x, t), u, r, b, n, cfn.names_away(ks, CronFileView.id_of(j), x, eqg, eq))

def cfn.rows_f(bb: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +ks: Maybe<&2, Nat>, +u: Nat, +r: Bool, +b: Bool, +n: Nat, +x: Nat, +eqg: {CronFile.names_spec(CronFileView.id_of(j), ks) == False{} : Bool}, eq: {Nat.is_eq(CronFileView.id_of(j), x) == bb : Bool}, ih: {CronFileView.row_at(x, CronFileView.finish_rows(t, CronFile.finish_js_spec(CronFileView.slots_of(t, u), ks, u, r, b, n), u)) == cfn.mrow(x, ks, LCfd.cfd.first(x, t), u, r, b, n) : Maybe<&2, CronFileView.FRow>}) -> {CronFileView.row_at.pick(bb, CronFileView.row_of(j, u), CronFileView.row_at(x, CronFileView.finish_rows(t, CronFile.finish_js_spec(CronFileView.slots_of(t, u), ks, u, r, b, n), u))) == cfn.mrow(x, ks, LCfd.cfd.first.pick(bb, j, LCfd.cfd.first(x, t)), u, r, b, n) : Maybe<&2, CronFileView.FRow>}:
  match bb:
    case True{}:
      %LCfl.cfl.eq_of(CronFileView.id_of(j), x, eq) : {Some{CronFileView.row_of(j, u)} == Some{CronFileView.fin_row(cfn.fin_of(CronFile.names_spec(_, ks), j, u, r, b, n), j, u)} : Maybe<&2, CronFileView.FRow>}
      %Equal.sym(Bool, CronFile.names_spec(CronFileView.id_of(j), ks), False{}, eqg) : {Some{CronFileView.row_of(j, u)} == Some{CronFileView.fin_row(cfn.fin_of(_, j, u, r, b, n), j, u)} : Maybe<&2, CronFileView.FRow>}
      {==}
    case False{}:
      ih

def cfn.rows_g(g: Bool, +j: Cr.Job, +t: List<&2, Cr.Rec>, +ks: Maybe<&2, Nat>, +u: Nat, +r: Bool, +b: Bool, +n: Nat, +x: Nat, +eqg: {CronFile.names_spec(CronFileView.id_of(j), ks) == g : Bool}, ih: {CronFileView.row_at(x, CronFileView.finish_rows(t, CronFile.finish_js_spec(CronFileView.slots_of(t, u), ks, u, r, b, n), u)) == cfn.mrow(x, ks, LCfd.cfd.first(x, t), u, r, b, n) : Maybe<&2, CronFileView.FRow>}) -> {CronFileView.row_at(x, CronFileView.finish_rows(Cr.Known{j} <> t, CronFile.finish_js_spec.slot(g, Cron.fact_of(j, u), CronFileView.slots_of(t, u), u, r, b, n, CronFile.finish_js_spec(CronFileView.slots_of(t, u), ks, u, r, b, n)), u)) == cfn.mrow(x, ks, LCfd.cfd.first(x, Cr.Known{j} <> t), u, r, b, n) : Maybe<&2, CronFileView.FRow>}:
  match g:
    case True{}:
      +f = CronStore.finish_spec(u, Cron.fact_of(j, u), r, b, n)
      +rest = CronFileView.finish_rows(t, CronFile.untouched_spec(CronFileView.slots_of(t, u)), u)
      %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.fin_row(f, j, u) <> rest), CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.fin_row(f, j, u), CronFileView.row_at(x, rest)), cfn.fin_head(f, j, x, u, rest)) : {_ == cfn.mrow(x, ks, LCfd.cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, LCfd.cfd.first(x, t)), u, r, b, n) : Maybe<&2, CronFileView.FRow>}
      %Equal.sym(List<&2, CronFileView.FRow>, rest, CronFileView.rows_of(t, u), cfn.untouched_rows(t, u)) : {CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.fin_row(f, j, u), CronFileView.row_at(x, _)) == cfn.mrow(x, ks, LCfd.cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, LCfd.cfd.first(x, t)), u, r, b, n) : Maybe<&2, CronFileView.FRow>}
      %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.rows_of(t, u)), LCfd.cfd.mrow(LCfd.cfd.first(x, t), u), LCfd.cfd.rows_at(x, t, u)) : {CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.fin_row(f, j, u), _) == cfn.mrow(x, ks, LCfd.cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, LCfd.cfd.first(x, t)), u, r, b, n) : Maybe<&2, CronFileView.FRow>}
      cfn.rows_t(Nat.is_eq(CronFileView.id_of(j), x), j, t, ks, u, r, b, n, x, eqg, {==})
    case False{}:
      +rest = CronFileView.finish_rows(t, CronFile.finish_js_spec(CronFileView.slots_of(t, u), ks, u, r, b, n), u)
      %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.row_of(j, u) <> rest), CronFileView.row_at.pick(Nat.is_eq(CronFileView.id_of(j), x), CronFileView.row_of(j, u), CronFileView.row_at(x, rest)), LCfd.cfd.row_at_head(j, x, u, rest)) : {_ == cfn.mrow(x, ks, LCfd.cfd.first.pick(Nat.is_eq(CronFileView.id_of(j), x), j, LCfd.cfd.first(x, t)), u, r, b, n) : Maybe<&2, CronFileView.FRow>}
      cfn.rows_f(Nat.is_eq(CronFileView.id_of(j), x), j, t, ks, u, r, b, n, x, eqg, {==}, ih)

def cfn.rows(+x: Nat, rs: List<&2, Cr.Rec>, +ks: Maybe<&2, Nat>, +u: Nat, +r: Bool, +b: Bool, +n: Nat) -> {CronFileView.row_at(x, CronFileView.finish_rows(rs, CronFile.finish_js_spec(CronFileView.slots_of(rs, u), ks, u, r, b, n), u)) == cfn.mrow(x, ks, LCfd.cfd.first(x, rs), u, r, b, n) : Maybe<&2, CronFileView.FRow>}:
  match rs:
    case Nil{}:
      {==}
    case rr <> +t:
      match rr:
        case Cr.Known{+j}:
          cfn.rows_g(CronFile.names_spec(CronFileView.id_of(j), ks), j, t, ks, u, r, b, n, x, {==}, cfn.rows(x, t, ks, u, r, b, n))
        case Cr.Raw{y}:
          cfn.rows(x, t, ks, u, r, b, n)

def cfn.raw_fin(f: CS.Fin, j: Cr.Job, +u: Nat, rest: List<&2, CronFileView.FRow>) -> {CronFileView.raw_rows(CronFileView.fin_row(f, j, u) <> rest) == CronFileView.raw_rows(rest) : List<&2, Nat>}:
  match f:
    case CS.Untouched{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Ran{st2, nn, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Skipped{st2, nn, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

def cfn.raws(rs: List<&2, Cr.Rec>, fs: List<&2, CS.Fin>, +u: Nat) -> {CronFileView.raw_rows(CronFileView.finish_rows(rs, fs, u)) == CronFileView.raw_rows(CronFileView.rows_of(rs, u)) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{+j}:
          match fs:
            case Nil{}:
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.finish_rows(t, Nil{}, u)), CronFileView.raw_rows(CronFileView.finish_rows(t, Nil{}, u)), LCfd.cfd.raw_head(j, u, CronFileView.finish_rows(t, Nil{}, u))) : {_ == CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)) : List<&2, Nat>}
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.raw_rows(CronFileView.rows_of(t, u)), LCfd.cfd.raw_head(j, u, CronFileView.rows_of(t, u))) : {CronFileView.raw_rows(CronFileView.finish_rows(t, Nil{}, u)) == _ : List<&2, Nat>}
              cfn.raws(t, Nil{}, u)
            case +f <> +rest:
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.fin_row(f, j, u) <> CronFileView.finish_rows(t, rest, u)), CronFileView.raw_rows(CronFileView.finish_rows(t, rest, u)), cfn.raw_fin(f, j, u, CronFileView.finish_rows(t, rest, u))) : {_ == CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)) : List<&2, Nat>}
              %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.row_of(j, u) <> CronFileView.rows_of(t, u)), CronFileView.raw_rows(CronFileView.rows_of(t, u)), LCfd.cfd.raw_head(j, u, CronFileView.rows_of(t, u))) : {CronFileView.raw_rows(CronFileView.finish_rows(t, rest, u)) == _ : List<&2, Nat>}
              cfn.raws(t, rest, u)
        case Cr.Raw{+y}:
          %cfn.raws(t, fs, u) : {y <> CronFileView.raw_rows(CronFileView.finish_rows(t, fs, u)) == y <> _ : List<&2, Nat>}
          {==}

# The claim records kept
# ----------------------

def cfn.mm_pick(g: Bool, l: List<&2, Cr.Claim>) -> List<&2, Cr.Claim>:
  match g:
    case True{}:
      Nil{}
    case False{}:
      l

# the claim records naming x a finish step of p's run of job ji keeps: the
# first job of id x's claim, unless x is ji and that claim is p's and run
def cfn.mmarks(+x: Nat, +ji: Nat, +p: Nat, m: Maybe<&2, Cr.Job>, +u: Nat) -> List<&2, Cr.Claim>:
  match m:
    case None{}:
      Nil{}
    case Some{+j}:
      cfn.mm_pick(Bool.and(Nat.is_eq(x, ji), cfn.owned(p, j)), LCfd.cfd.own(j, u))

def cfn.mm_nil(g: Bool) -> {cfn.mm_pick(g, Nil{}) == Nil{} : List<&2, Cr.Claim>}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def cfn.mm_off(+x: Nat, +ji: Nat, +p: Nat, m: Maybe<&2, Cr.Job>, +u: Nat, ne: {Nat.is_eq(x, ji) == False{} : Bool}) -> {LCfd.cfd.mclaims(m, u) == cfn.mmarks(x, ji, p, m, u) : List<&2, Cr.Claim>}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      %Equal.sym(Bool, Nat.is_eq(x, ji), False{}, ne) : {LCfd.cfd.own(j, u) == cfn.mm_pick(Bool.and(_, cfn.owned(p, j)), LCfd.cfd.own(j, u)) : List<&2, Cr.Claim>}
      {==}

def cfn.sel_nil(xs: List<&2, Bool>) -> {CronFileView.select_marks(Nil{}, xs) == Nil{} : List<&2, CronFileView.FClaim>}:
  match xs:
    case Nil{}:
      {==}
    case y <> t:
      {==}

def cfn.sel_stays(t: List<&2, Cr.Rec>, +p: Nat, +ji: Nat, +u: Nat, +xs: List<&2, Bool>) -> {CronFileView.select_marks(CronFileView.marks_of(t, u), List.append(&2, Bool, CronFile.stays_spec(CronFileView.pins_of(p, ji, t)), xs)) == CronFileView.marks_of(t, u) : List<&2, CronFileView.FClaim>}:
  match t:
    case Nil{}:
      cfn.sel_nil(xs)
    case r <> +rest:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, s, st, nx, k, cl, ru, ss, h}:
              match cl:
                case None{}:
                  cfn.sel_stays(rest, p, ji, u, xs)
                case Some{c}:
                  match c:
                    case Cr.Claim{+o, +w}:
                      %Equal.sym(List<&2, CronFileView.FClaim>, CronFileView.select_marks(CronFileView.marks_of(rest, u), List.append(&2, Bool, CronFile.stays_spec(CronFileView.pins_of(p, ji, rest)), xs)), CronFileView.marks_of(rest, u), cfn.sel_stays(rest, p, ji, u, xs)) : {CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}} <> _ == CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}} <> CronFileView.marks_of(rest, u) : List<&2, CronFileView.FClaim>}
                      {==}
        case Cr.Raw{y}:
          cfn.sel_stays(rest, p, ji, u, xs)

def cfn.marks_nocl(bb: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +ji: Nat, +x: Nat, +t: List<&2, Cr.Rec>, +ks: List<&2, Bool>, +u: Nat, +eq: {Nat.is_eq(i, x) == bb : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks)) == cfn.mmarks(x, ji, p, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks)) == cfn.mmarks(x, ji, p, LCfd.cfd.first.pick(bb, Cr.Job{i, s, st, nx, k, None{}, ru, ss, h}, LCfd.cfd.first(x, t)), u) : List<&2, Cr.Claim>}:
  match bb:
    case True{}:
      %Equal.sym(List<&2, Cr.Claim>, cfn.mm_pick(Bool.and(Nat.is_eq(x, ji), False{}), Nil{}), Nil{}, cfn.mm_nil(Bool.and(Nat.is_eq(x, ji), False{}))) : {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks)) == _ : List<&2, Cr.Claim>}
      LCrv.crv.marks_none(x, t, ks, u, LCfd.cfd.has_move(i, x, t, LCfl.cfl.eq_of(i, x, eq), nt))
    case False{}:
      ih

def cfn.marks_ht(bb: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +o: Nat, +w: Nat, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +ji: Nat, +x: Nat, +t: List<&2, Cr.Rec>, +u: Nat, +eqh: {Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))) == True{} : Bool}, +eq: {Nat.is_eq(i, x) == bb : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, +dt: {CronFileView.distinct(t) == True{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.marks_of(t, u)) == cfn.mmarks(x, ji, p, LCfd.cfd.first.pick(bb, Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h}, LCfd.cfd.first(x, t)), u) : List<&2, Cr.Claim>}:
  match bb:
    case True{}:
      +ix = LCfl.cfl.eq_of(i, x, eq)
      %ix : {CronFileView.marks_at(x, CronFileView.marks_of(t, u)) == cfn.mm_pick(Bool.and(Nat.is_eq(_, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), [Cr.Claim{Nat.mul(o, u), w}]) : List<&2, Cr.Claim>}
      %Equal.sym(Bool, Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), True{}, eqh) : {CronFileView.marks_at(x, CronFileView.marks_of(t, u)) == cfn.mm_pick(_, [Cr.Claim{Nat.mul(o, u), w}]) : List<&2, Cr.Claim>}
      LCfd.cfd.marks_none(x, t, u, LCfd.cfd.has_move(i, x, t, ix, nt))
    case False{}:
      +ij = LCfl.cfl.eq_of(i, ji, LCfl.cfl.and_l(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru)), eqh))
      +ne = Equal.trans(Bool, Nat.is_eq(x, ji), Nat.is_eq(x, i), False{}, Equal.cong(Nat, Bool, y => Nat.is_eq(x, y), ji, i, Equal.sym(Nat, i, ji, ij)), LCfl.cfl.ne_comm(i, x, eq))
      %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.marks_of(t, u)), LCfd.cfd.mclaims(LCfd.cfd.first(x, t), u), LCfd.cfd.marks_at(x, t, u, dt)) : {_ == cfn.mmarks(x, ji, p, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}
      cfn.mm_off(x, ji, p, LCfd.cfd.first(x, t), u, ne)

def cfn.marks_hf(bb: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +o: Nat, +w: Nat, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +ji: Nat, +x: Nat, +t: List<&2, Cr.Rec>, +ks: List<&2, Bool>, +u: Nat, +eqh: {Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))) == False{} : Bool}, +eq: {Nat.is_eq(i, x) == bb : Bool}, nt: {CronFileView.has_id(i, t) == False{} : Bool}, ih: {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks)) == cfn.mmarks(x, ji, p, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}) -> {CronFileView.marks_at.pick(Nat.is_eq(i, x), Cr.Claim{Nat.mul(o, u), w}, CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks))) == cfn.mmarks(x, ji, p, LCfd.cfd.first.pick(bb, Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h}, LCfd.cfd.first(x, t)), u) : List<&2, Cr.Claim>}:
  match bb:
    case True{}:
      +ix = LCfl.cfl.eq_of(i, x, eq)
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, eq) : {CronFileView.marks_at.pick(_, Cr.Claim{Nat.mul(o, u), w}, CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks))) == cfn.mmarks(x, ji, p, Some{Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h}}, u) : List<&2, Cr.Claim>}
      %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks)), Nil{}, LCrv.crv.marks_none(x, t, ks, u, LCfd.cfd.has_move(i, x, t, ix, nt))) : {Cr.Claim{Nat.mul(o, u), w} <> _ == cfn.mm_pick(Bool.and(Nat.is_eq(x, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), [Cr.Claim{Nat.mul(o, u), w}]) : List<&2, Cr.Claim>}
      %ix : {[Cr.Claim{Nat.mul(o, u), w}] == cfn.mm_pick(Bool.and(Nat.is_eq(_, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), [Cr.Claim{Nat.mul(o, u), w}]) : List<&2, Cr.Claim>}
      %Equal.sym(Bool, Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), False{}, eqh) : {[Cr.Claim{Nat.mul(o, u), w}] == cfn.mm_pick(_, [Cr.Claim{Nat.mul(o, u), w}]) : List<&2, Cr.Claim>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), False{}, eq) : {CronFileView.marks_at.pick(_, Cr.Claim{Nat.mul(o, u), w}, CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), ks))) == cfn.mmarks(x, ji, p, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}
      ih

def cfn.marks_h(hj: Bool, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, +o: Nat, +w: Nat, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +p: Nat, +ji: Nat, +x: Nat, +t: List<&2, Cr.Rec>, +xs: List<&2, Bool>, +u: Nat, +eqh: {Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))) == hj : Bool}, +nt: {CronFileView.has_id(i, t) == False{} : Bool}, +dt: {CronFileView.distinct(t) == True{} : Bool}, ih: {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(t, u), List.append(&2, Bool, CronFile.drops_spec(CronFileView.pins_of(p, ji, t)), xs))) == cfn.mmarks(x, ji, p, LCfd.cfd.first(x, t), u) : List<&2, Cr.Claim>}) -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}} <> CronFileView.marks_of(t, u), List.append(&2, Bool, CronFile.drops_spec.pin(hj, CronFileView.pins_of(p, ji, t), CronFile.drops_spec(CronFileView.pins_of(p, ji, t))), xs))) == cfn.mmarks(x, ji, p, LCfd.cfd.first.pick(Nat.is_eq(i, x), Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h}, LCfd.cfd.first(x, t)), u) : List<&2, Cr.Claim>}:
  match hj:
    case True{}:
      %Equal.sym(List<&2, CronFileView.FClaim>, CronFileView.select_marks(CronFileView.marks_of(t, u), List.append(&2, Bool, CronFile.stays_spec(CronFileView.pins_of(p, ji, t)), xs)), CronFileView.marks_of(t, u), cfn.sel_stays(t, p, ji, u, xs)) : {CronFileView.marks_at(x, _) == cfn.mmarks(x, ji, p, LCfd.cfd.first.pick(Nat.is_eq(i, x), Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h}, LCfd.cfd.first(x, t)), u) : List<&2, Cr.Claim>}
      cfn.marks_ht(Nat.is_eq(i, x), i, s, st, nx, k, o, w, ru, ss, h, p, ji, x, t, u, eqh, {==}, nt, dt)
    case False{}:
      cfn.marks_hf(Nat.is_eq(i, x), i, s, st, nx, k, o, w, ru, ss, h, p, ji, x, t, List.append(&2, Bool, CronFile.drops_spec(CronFileView.pins_of(p, ji, t)), xs), u, eqh, {==}, nt, ih)

# no two jobs share an id: the claim records naming x a finish step keeps
def cfn.marks(+x: Nat, +p: Nat, +ji: Nat, rs: List<&2, Cr.Rec>, +xs: List<&2, Bool>, +u: Nat, +d: {CronFileView.distinct(rs) == True{} : Bool}) -> {CronFileView.marks_at(x, CronFileView.select_marks(CronFileView.marks_of(rs, u), List.append(&2, Bool, CronFile.drops_spec(CronFileView.pins_of(p, ji, rs)), xs))) == cfn.mmarks(x, ji, p, LCfd.cfd.first(x, rs), u) : List<&2, Cr.Claim>}:
  match rs:
    case Nil{}:
      LCrv.crv.marks_nil(x, xs, u)
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, +s, +st, +nx, +k, cl, +ru, +ss, +h}:
              match cl:
                case None{}:
                  +jj = {Cr.Job{i, s, st, nx, k, None{}, ru, ss, h} : Cr.Job}
                  cfn.marks_nocl(Nat.is_eq(i, x), i, s, st, nx, k, ru, ss, h, p, ji, x, t, List.append(&2, Bool, CronFile.drops_spec(CronFileView.pins_of(p, ji, t)), xs), u, {==}, LCfd.cfd.distinct_head(jj, t, d), cfn.marks(x, p, ji, t, xs, u, LCfd.cfd.distinct_tail(jj, t, d)))
                case Some{c}:
                  match c:
                    case Cr.Claim{+o, +w}:
                      +jj = {Cr.Job{i, s, st, nx, k, Some{Cr.Claim{o, w}}, ru, ss, h} : Cr.Job}
                      cfn.marks_h(Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), i, s, st, nx, k, o, w, ru, ss, h, p, ji, x, t, xs, u, {==}, LCfd.cfd.distinct_head(jj, t, d), LCfd.cfd.distinct_tail(jj, t, d), cfn.marks(x, p, ji, t, xs, u, LCfd.cfd.distinct_tail(jj, t, d)))
        case Cr.Raw{y}:
          cfn.marks(x, p, ji, t, xs, u, d)

# The claim records this build cannot read
# ----------------------------------------

def cfn.stays_app(a: List<&2, CF.Pin>, +b: List<&2, CF.Pin>) -> {CronFile.stays_spec(List.append(&2, CF.Pin, a, b)) == List.append(&2, Bool, CronFile.stays_spec(a), CronFile.stays_spec(b)) : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case c <> +t:
      %Equal.sym(List<&2, Bool>, CronFile.stays_spec(List.append(&2, CF.Pin, t, b)), List.append(&2, Bool, CronFile.stays_spec(t), CronFile.stays_spec(b)), cfn.stays_app(t, b)) : {True{} <> _ == True{} <> List.append(&2, Bool, CronFile.stays_spec(t), CronFile.stays_spec(b)) : List<&2, Bool>}
      {==}

def cfn.drops_unpinned(rd: List<&2, Nat>) -> {CronFile.drops_spec(CronFileView.unpinned(rd)) == CronFile.stays_spec(CronFileView.unpinned(rd)) : List<&2, Bool>}:
  match rd:
    case Nil{}:
      {==}
    case y <> t:
      %Equal.sym(List<&2, Bool>, CronFile.drops_spec(CronFileView.unpinned(t)), CronFile.stays_spec(CronFileView.unpinned(t)), cfn.drops_unpinned(t)) : {True{} <> _ == True{} <> CronFile.stays_spec(CronFileView.unpinned(t)) : List<&2, Bool>}
      {==}

def cfn.drops_app_pin(h: Bool, +t: List<&2, CF.Pin>, +rd: List<&2, Nat>, ih: {CronFile.drops_spec(List.append(&2, CF.Pin, t, CronFileView.unpinned(rd))) == List.append(&2, Bool, CronFile.drops_spec(t), CronFile.stays_spec(CronFileView.unpinned(rd))) : List<&2, Bool>}) -> {CronFile.drops_spec.pin(h, List.append(&2, CF.Pin, t, CronFileView.unpinned(rd)), CronFile.drops_spec(List.append(&2, CF.Pin, t, CronFileView.unpinned(rd)))) == List.append(&2, Bool, CronFile.drops_spec.pin(h, t, CronFile.drops_spec(t)), CronFile.stays_spec(CronFileView.unpinned(rd))) : List<&2, Bool>}:
  match h:
    case True{}:
      %Equal.sym(List<&2, Bool>, CronFile.stays_spec(List.append(&2, CF.Pin, t, CronFileView.unpinned(rd))), List.append(&2, Bool, CronFile.stays_spec(t), CronFile.stays_spec(CronFileView.unpinned(rd))), cfn.stays_app(t, CronFileView.unpinned(rd))) : {False{} <> _ == False{} <> List.append(&2, Bool, CronFile.stays_spec(t), CronFile.stays_spec(CronFileView.unpinned(rd))) : List<&2, Bool>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Bool>, CronFile.drops_spec(List.append(&2, CF.Pin, t, CronFileView.unpinned(rd))), List.append(&2, Bool, CronFile.drops_spec(t), CronFile.stays_spec(CronFileView.unpinned(rd))), ih) : {True{} <> _ == True{} <> List.append(&2, Bool, CronFile.drops_spec(t), CronFile.stays_spec(CronFileView.unpinned(rd))) : List<&2, Bool>}
      {==}

def cfn.drops_app(a: List<&2, CF.Pin>, +rd: List<&2, Nat>) -> {CronFile.drops_spec(List.append(&2, CF.Pin, a, CronFileView.unpinned(rd))) == List.append(&2, Bool, CronFile.drops_spec(a), CronFile.stays_spec(CronFileView.unpinned(rd))) : List<&2, Bool>}:
  match a:
    case Nil{}:
      cfn.drops_unpinned(rd)
    case c <> +t:
      match c:
        case CF.Pinned{m, +h}:
          cfn.drops_app_pin(h, t, rd, cfn.drops_app(t, rd))
        case CF.Unpinned{}:
          %Equal.sym(List<&2, Bool>, CronFile.drops_spec(List.append(&2, CF.Pin, t, CronFileView.unpinned(rd))), List.append(&2, Bool, CronFile.drops_spec(t), CronFile.stays_spec(CronFileView.unpinned(rd))), cfn.drops_app(t, rd)) : {True{} <> _ == True{} <> List.append(&2, Bool, CronFile.drops_spec(t), CronFile.stays_spec(CronFileView.unpinned(rd))) : List<&2, Bool>}
          {==}

def cfn.after_stays(t: List<&2, Cr.Rec>, +p: Nat, +ji: Nat, +u: Nat, +ys: List<&2, Bool>) -> {CronFileView.after_marks(CronFileView.marks_of(t, u), List.append(&2, Bool, CronFile.stays_spec(CronFileView.pins_of(p, ji, t)), ys)) == ys : List<&2, Bool>}:
  match t:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{i, s, st, nx, k, cl, ru, ss, h}:
              match cl:
                case None{}:
                  cfn.after_stays(rest, p, ji, u, ys)
                case Some{c}:
                  match c:
                    case Cr.Claim{o, w}:
                      cfn.after_stays(rest, p, ji, u, ys)
        case Cr.Raw{y}:
          cfn.after_stays(rest, p, ji, u, ys)

def cfn.after_h(hj: Bool, +t: List<&2, Cr.Rec>, +p: Nat, +ji: Nat, +u: Nat, +ys: List<&2, Bool>, +m: CronFileView.FClaim, ih: {CronFileView.after_marks(CronFileView.marks_of(t, u), List.append(&2, Bool, CronFile.drops_spec(CronFileView.pins_of(p, ji, t)), ys)) == ys : List<&2, Bool>}) -> {CronFileView.after_marks(m <> CronFileView.marks_of(t, u), List.append(&2, Bool, CronFile.drops_spec.pin(hj, CronFileView.pins_of(p, ji, t), CronFile.drops_spec(CronFileView.pins_of(p, ji, t))), ys)) == ys : List<&2, Bool>}:
  match hj:
    case True{}:
      cfn.after_stays(t, p, ji, u, ys)
    case False{}:
      ih

def cfn.after_drops(rs: List<&2, Cr.Rec>, +p: Nat, +ji: Nat, +u: Nat, +ys: List<&2, Bool>) -> {CronFileView.after_marks(CronFileView.marks_of(rs, u), List.append(&2, Bool, CronFile.drops_spec(CronFileView.pins_of(p, ji, rs)), ys)) == ys : List<&2, Bool>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Cr.Known{j}:
          match j:
            case Cr.Job{+i, s, st, nx, k, cl, +ru, ss, h}:
              match cl:
                case None{}:
                  cfn.after_drops(t, p, ji, u, ys)
                case Some{c}:
                  match c:
                    case Cr.Claim{+o, +w}:
                      cfn.after_h(Bool.and(Nat.is_eq(i, ji), Bool.and(Nat.is_eq(w, p), Cr.has(p, ru))), t, p, ji, u, ys, CronFileView.FClaim{i, Cr.Claim{Nat.mul(o, u), w}}, cfn.after_drops(t, p, ji, u, ys))
        case Cr.Raw{y}:
          cfn.after_drops(t, p, ji, u, ys)

def cfn.raws_stay(rd: List<&2, Nat>) -> {CronFileView.select_raws(rd, CronFile.stays_spec(CronFileView.unpinned(rd))) == rd : List<&2, Nat>}:
  match rd:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(List<&2, Nat>, CronFileView.select_raws(t, CronFile.stays_spec(CronFileView.unpinned(t))), t, cfn.raws_stay(t)) : {y <> _ == y <> t : List<&2, Nat>}
      {==}

# A finish step that is not p's, or not run, changes nothing the file holds
# -------------------------------------------------------------------------

def cfn.and_t(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cfn.noop_run(b1: Bool, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, cl: Maybe<&2, Cr.Claim>, +rs: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +u: Nat, +eq1: {Cr.has(p, rs) == b1 : Bool}, no: {cfn.owned(p, Cr.Job{i, s, st, nx, k, cl, rs, ss, h}) == False{} : Bool}) -> {Cron.view(Cr.finish.run(b1, p, c, o, i, s, st, nx, k, cl, rs, ss, h), u) == Cron.view(Cr.Job{i, s, st, nx, k, cl, rs, ss, h}, u) : Cron.View()}:
  match b1:
    case False{}:
      {==}
    case True{}:
      match cl:
        case None{}:
          {==}
        case Some{c0}:
          match c0:
            case Cr.Claim{+oc, +w}:
              +e1 = Equal.cong(Bool, Bool, y => Bool.and(Nat.is_eq(w, p), y), Cr.has(p, rs), True{}, eq1)
              +e2 = Equal.trans(Bool, Bool.and(Nat.is_eq(w, p), True{}), Bool.and(Nat.is_eq(w, p), Cr.has(p, rs)), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(w, p), Cr.has(p, rs)), Bool.and(Nat.is_eq(w, p), True{}), e1), no)
              +nw = Equal.trans(Bool, Nat.is_eq(w, p), Bool.and(Nat.is_eq(w, p), True{}), False{}, Equal.sym(Bool, Bool.and(Nat.is_eq(w, p), True{}), Nat.is_eq(w, p), cfn.and_t(Nat.is_eq(w, p))), e2)
              %Equal.sym(Bool, Nat.is_eq(w, p), False{}, nw) : {Cron.view(Cr.finish.own(_, Cr.Claim{oc, w}, c, o, i, s, st, nx, k, Cr.drop(p, rs), ss, h), u) == Cron.view(Cr.Job{i, s, st, nx, k, Some{Cr.Claim{oc, w}}, rs, ss, h}, u) : Cron.View()}
              {==}

def cfn.noop(+p: Nat, +c: Nat, +o: Cr.Out, j: Cr.Job, +u: Nat, no: {cfn.owned(p, j) == False{} : Bool}) -> {Cron.view(Cr.finish(p, c, o, j), u) == Cron.view(j, u) : Cron.View()}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +rs, +ss, +h}:
      cfn.noop_run(Cr.has(p, rs), p, c, o, i, s, st, nx, k, cl, rs, ss, h, u, {==}, no)

def cfn.row_fin(f: CS.Fin, j: Cr.Job, +u: Nat) -> {CronFileView.fin_row(f, j, u) == LCfd.cfd.prow(CronFileView.id_of(j), Cron.fin_view(f, j, u)) : CronFileView.FRow}:
  match f:
    case CS.Untouched{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Ran{st2, nn, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Skipped{st2, nn, k2}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}

def cfn.pcl_fin(f: CS.Fin, j: Cr.Job, +u: Nat) -> {LCfd.cfd.pcl(Cron.fin_view(f, j, u)) == Nil{} : List<&2, Cr.Claim>}:
  match f:
    case CS.Untouched{}:
      match j:
        case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
          {==}
    case CS.Ran{st2, nn, k2}:
      {==}
    case CS.Skipped{st2, nn, k2}:
      {==}

def cfn.id_finish(+p: Nat, +c: Nat, +o: Cr.Out, +j: Cr.Job) -> {CronFileView.id_of(Cr.finish(p, c, o, j)) == CronFileView.id_of(j) : Nat}:
  %Equal.sym(Nat, CronFileView.id_of(Cr.finish(p, c, o, j)), Cr.Job.id(Cr.finish(p, c, o, j)), LCfd.cfd.id_eq(Cr.finish(p, c, o, j))) : {_ == CronFileView.id_of(j) : Nat}
  %Equal.sym(Nat, CronFileView.id_of(j), Cr.Job.id(j), LCfd.cfd.id_eq(j)) : {Cr.Job.id(Cr.finish(p, c, o, j)) == _ : Nat}
  LACron.pc.id_finish(p, c, o, j)

# One job
# -------

# the finish step of p's run of the first job of id x, p's and run
def cfn.on_own(+v: Nat, +p: Nat, +c: Nat, +o: Cr.Out, +i: Nat, +s: Cr.Sched, +st: Cr.Status, +nx: Maybe<&2, Nat>, +k: Nat, cl: Maybe<&2, Cr.Claim>, +ru: List<&2, Nat>, +ss: List<&2, Nat>, +h: List<&2, Cr.Mark>, +r3: List<&2, Nat>, +rd: List<&2, Nat>, +eqo: {cfn.owned(p, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}) == True{} : Bool}) -> {(Some{CronFileView.fin_row(CronStore.finish_spec(1n+v, Cron.fact_of(Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, 1n+v), Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, 1n+v)}, (Nil{}, (r3, rd))) == (Some{CronFileView.row_of(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}), 1n+v)}, (LCfd.cfd.own(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match cl:
    case None{}:
      LCfl.cfl.absurdF({(Some{CronFileView.fin_row(CronStore.finish_spec(1n+v, Cron.fact_of(Cr.Job{i, s, st, nx, k, None{}, ru, ss, h}, 1n+v), Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, None{}, ru, ss, h}, 1n+v)}, (Nil{}, (r3, rd))) == (Some{CronFileView.row_of(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, None{}, ru, ss, h}), 1n+v)}, (LCfd.cfd.own(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, None{}, ru, ss, h}), 1n+v), (r3, rd))) : CronFileView.Obs()}, eqo)
    case Some{c0}:
      match c0:
        case Cr.Claim{+oc, +w}:
          +u = {1n+v : Nat}
          +j = {Cr.Job{i, s, st, nx, k, Some{Cr.Claim{oc, w}}, ru, ss, h} : Cr.Job}
          +f = CronStore.finish_spec(u, Cron.fact_of(j, u), Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, u))
          -fv = Cron.fin_view(f, j, u)
          -vv = Cron.view(Cr.finish(p, c, o, j), u)
          +wp = LCfl.cfl.eq_of(w, p, LCfl.cfl.and_l(Nat.is_eq(w, p), Cr.has(p, ru), eqo))
          +run = LCfl.cfl.and_r(Nat.is_eq(w, p), Cr.has(p, ru), eqo)
          +own = Equal.cong(Nat, Maybe<&2, Cr.Claim>, y => Some{Cr.Claim{oc, y}}, w, p, wp)
          %Equal.sym(CronFileView.FRow, CronFileView.row_of(Cr.finish(p, c, o, j), u), LCfd.cfd.prow(CronFileView.id_of(Cr.finish(p, c, o, j)), vv), LCfd.cfd.row_view(Cr.finish(p, c, o, j), u)) : {(Some{CronFileView.fin_row(f, j, u)}, (Nil{}, (r3, rd))) == (Some{_}, (LCfd.cfd.own(Cr.finish(p, c, o, j), u), (r3, rd))) : CronFileView.Obs()}
          %Equal.sym(List<&2, Cr.Claim>, LCfd.cfd.own(Cr.finish(p, c, o, j), u), LCfd.cfd.pcl(vv), LCfd.cfd.own_view(Cr.finish(p, c, o, j), u)) : {(Some{CronFileView.fin_row(f, j, u)}, (Nil{}, (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(Cr.finish(p, c, o, j)), vv)}, (_, (r3, rd))) : CronFileView.Obs()}
          %Cron.cron_finish_refines(v, p, c, o, oc, j, run, own) : {(Some{CronFileView.fin_row(f, j, u)}, (Nil{}, (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(Cr.finish(p, c, o, j)), _)}, (LCfd.cfd.pcl(_), (r3, rd))) : CronFileView.Obs()}
          %Equal.sym(Nat, CronFileView.id_of(Cr.finish(p, c, o, j)), CronFileView.id_of(j), cfn.id_finish(p, c, o, j)) : {(Some{CronFileView.fin_row(f, j, u)}, (Nil{}, (r3, rd))) == (Some{LCfd.cfd.prow(_, fv)}, (LCfd.cfd.pcl(fv), (r3, rd))) : CronFileView.Obs()}
          %Equal.sym(List<&2, Cr.Claim>, LCfd.cfd.pcl(fv), Nil{}, cfn.pcl_fin(f, j, u)) : {(Some{CronFileView.fin_row(f, j, u)}, (Nil{}, (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(j), fv)}, (_, (r3, rd))) : CronFileView.Obs()}
          %Equal.sym(CronFileView.FRow, CronFileView.fin_row(f, j, u), LCfd.cfd.prow(CronFileView.id_of(j), fv), cfn.row_fin(f, j, u)) : {(Some{_}, (Nil{}, (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(j), fv)}, (Nil{}, (r3, rd))) : CronFileView.Obs()}
          {==}

def cfn.on_true(+v: Nat, +p: Nat, +c: Nat, +o: Cr.Out, +x: Nat, j: Cr.Job, +r3: List<&2, Nat>, +rd: List<&2, Nat>, eqo: {cfn.owned(p, j) == True{} : Bool}) -> {(Some{CronFileView.fin_row(cfn.fin_of(CronFile.names_spec(x, Some{x}), j, 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), j, 1n+v)}, (Nil{}, (r3, rd))) == (Some{CronFileView.row_of(Cr.finish(p, c, o, j), 1n+v)}, (LCfd.cfd.own(Cr.finish(p, c, o, j), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match j:
    case Cr.Job{+i, +s, +st, +nx, +k, +cl, +ru, +ss, +h}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, LCfl.cfl.eq_refl(x)) : {(Some{CronFileView.fin_row(cfn.fin_of(_, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), Cr.Job{i, s, st, nx, k, cl, ru, ss, h}, 1n+v)}, (Nil{}, (r3, rd))) == (Some{CronFileView.row_of(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}), 1n+v)}, (LCfd.cfd.own(Cr.finish(p, c, o, Cr.Job{i, s, st, nx, k, cl, ru, ss, h}), 1n+v), (r3, rd))) : CronFileView.Obs()}
      cfn.on_own(v, p, c, o, i, s, st, nx, k, cl, ru, ss, h, r3, rd, eqo)

def cfn.on_ow(ow: Bool, +v: Nat, +p: Nat, +c: Nat, +o: Cr.Out, +x: Nat, +j: Cr.Job, +r3: List<&2, Nat>, +rd: List<&2, Nat>, eqo: {cfn.owned(p, j) == ow : Bool}) -> {(Some{CronFileView.fin_row(cfn.fin_of(CronFile.names_spec(x, cfn.hk(ow, x)), j, 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), j, 1n+v)}, (cfn.mm_pick(ow, LCfd.cfd.own(j, 1n+v)), (r3, rd))) == (Some{CronFileView.row_of(Cr.finish(p, c, o, j), 1n+v)}, (LCfd.cfd.own(Cr.finish(p, c, o, j), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match ow:
    case True{}:
      cfn.on_true(v, p, c, o, x, j, r3, rd, eqo)
    case False{}:
      +u = {1n+v : Nat}
      -vv = Cron.view(Cr.finish(p, c, o, j), u)
      -vj = Cron.view(j, u)
      %Equal.sym(CronFileView.FRow, CronFileView.row_of(Cr.finish(p, c, o, j), u), LCfd.cfd.prow(CronFileView.id_of(Cr.finish(p, c, o, j)), vv), LCfd.cfd.row_view(Cr.finish(p, c, o, j), u)) : {(Some{CronFileView.row_of(j, u)}, (LCfd.cfd.own(j, u), (r3, rd))) == (Some{_}, (LCfd.cfd.own(Cr.finish(p, c, o, j), u), (r3, rd))) : CronFileView.Obs()}
      %Equal.sym(List<&2, Cr.Claim>, LCfd.cfd.own(Cr.finish(p, c, o, j), u), LCfd.cfd.pcl(vv), LCfd.cfd.own_view(Cr.finish(p, c, o, j), u)) : {(Some{CronFileView.row_of(j, u)}, (LCfd.cfd.own(j, u), (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(Cr.finish(p, c, o, j)), vv)}, (_, (r3, rd))) : CronFileView.Obs()}
      %Equal.sym(Cron.View(), vv, vj, cfn.noop(p, c, o, j, u, eqo)) : {(Some{CronFileView.row_of(j, u)}, (LCfd.cfd.own(j, u), (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(Cr.finish(p, c, o, j)), _)}, (LCfd.cfd.pcl(_), (r3, rd))) : CronFileView.Obs()}
      %Equal.sym(Nat, CronFileView.id_of(Cr.finish(p, c, o, j)), CronFileView.id_of(j), cfn.id_finish(p, c, o, j)) : {(Some{CronFileView.row_of(j, u)}, (LCfd.cfd.own(j, u), (r3, rd))) == (Some{LCfd.cfd.prow(_, vj)}, (LCfd.cfd.pcl(vj), (r3, rd))) : CronFileView.Obs()}
      %Equal.sym(CronFileView.FRow, CronFileView.row_of(j, u), LCfd.cfd.prow(CronFileView.id_of(j), vj), LCfd.cfd.row_view(j, u)) : {(Some{_}, (LCfd.cfd.own(j, u), (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(j), vj)}, (LCfd.cfd.pcl(vj), (r3, rd))) : CronFileView.Obs()}
      %Equal.sym(List<&2, Cr.Claim>, LCfd.cfd.own(j, u), LCfd.cfd.pcl(vj), LCfd.cfd.own_view(j, u)) : {(Some{LCfd.cfd.prow(CronFileView.id_of(j), vj)}, (_, (r3, rd))) == (Some{LCfd.cfd.prow(CronFileView.id_of(j), vj)}, (LCfd.cfd.pcl(vj), (r3, rd))) : CronFileView.Obs()}
      {==}

# Job by job
# ----------

def cfn.nh(ow: Bool, +x: Nat, +ji: Nat, ne: {Nat.is_eq(x, ji) == False{} : Bool}) -> {CronFile.names_spec(x, cfn.hk(ow, ji)) == False{} : Bool}:
  match ow:
    case True{}:
      ne
    case False{}:
      {==}

def cfn.names_hit_off(+x: Nat, +ji: Nat, +p: Nat, m: Maybe<&2, Cr.Job>, ne: {Nat.is_eq(x, ji) == False{} : Bool}) -> {CronFile.names_spec(x, cfn.mhit(p, ji, m)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      cfn.nh(cfn.owned(p, j), x, ji, ne)

def cfn.id_job_eq(+j: Cr.Job, +x: Nat, idm: {Nat.is_eq(CronFileView.id_of(j), x) == True{} : Bool}) -> {Cr.Job.id(j) == x : Nat}:
  Equal.trans(Nat, Cr.Job.id(j), CronFileView.id_of(j), x, Equal.sym(Nat, CronFileView.id_of(j), Cr.Job.id(j), LCfd.cfd.id_eq(j)), LCfl.cfl.eq_of(CronFileView.id_of(j), x, idm))

def cfn.off_m(+v: Nat, +p: Nat, +c: Nat, +ji: Nat, +o: Cr.Out, +x: Nat, +dead: List<&2, Nat>, m: Maybe<&2, Cr.Job>, +r3: List<&2, Nat>, +rd: List<&2, Nat>, idm: LCfd.cfd.IdIs(m, x), ne: {Nat.is_eq(x, ji) == False{} : Bool}) -> {(LCfd.cfd.mrow(m, 1n+v), (LCfd.cfd.mclaims(m, 1n+v), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, m), 1n+v), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, m), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      +ej = Equal.trans(Bool, Nat.is_eq(Cr.Job.id(j), ji), Nat.is_eq(x, ji), False{}, Equal.cong(Nat, Bool, y => Nat.is_eq(y, ji), Cr.Job.id(j), x, cfn.id_job_eq(j, x, idm)), ne)
      %Equal.sym(Bool, Nat.is_eq(Cr.Job.id(j), ji), False{}, ej) : {(Some{CronFileView.row_of(j, 1n+v)}, (LCfd.cfd.own(j, 1n+v), (r3, rd))) == (Some{CronFileView.row_of(Cr.job.pick(_, Cr.finish(p, c, o, j), j), 1n+v)}, (LCfd.cfd.own(Cr.job.pick(_, Cr.finish(p, c, o, j), j), 1n+v), (r3, rd))) : CronFileView.Obs()}
      {==}

def cfn.on_m(+v: Nat, +p: Nat, +c: Nat, +o: Cr.Out, +x: Nat, +dead: List<&2, Nat>, m: Maybe<&2, Cr.Job>, +r3: List<&2, Nat>, +rd: List<&2, Nat>, idm: LCfd.cfd.IdIs(m, x)) -> {(cfn.mrow(x, cfn.mhit(p, x, m), m, 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), (cfn.mmarks(x, x, p, m, 1n+v), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Finish{p, x, o}, c, dead, m), 1n+v), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Finish{p, x, o}, c, dead, m), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      +ej = Equal.trans(Bool, Nat.is_eq(Cr.Job.id(j), x), Nat.is_eq(x, x), True{}, Equal.cong(Nat, Bool, y => Nat.is_eq(y, x), Cr.Job.id(j), x, cfn.id_job_eq(j, x, idm)), LCfl.cfl.eq_refl(x))
      %Equal.sym(Bool, Nat.is_eq(Cr.Job.id(j), x), True{}, ej) : {(Some{CronFileView.fin_row(cfn.fin_of(CronFile.names_spec(x, cfn.hk(cfn.owned(p, j), x)), j, 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), j, 1n+v)}, (cfn.mm_pick(Bool.and(Nat.is_eq(x, x), cfn.owned(p, j)), LCfd.cfd.own(j, 1n+v)), (r3, rd))) == (Some{CronFileView.row_of(Cr.job.pick(_, Cr.finish(p, c, o, j), j), 1n+v)}, (LCfd.cfd.own(Cr.job.pick(_, Cr.finish(p, c, o, j), j), 1n+v), (r3, rd))) : CronFileView.Obs()}
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, LCfl.cfl.eq_refl(x)) : {(Some{CronFileView.fin_row(cfn.fin_of(CronFile.names_spec(x, cfn.hk(cfn.owned(p, j), x)), j, 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), j, 1n+v)}, (cfn.mm_pick(Bool.and(_, cfn.owned(p, j)), LCfd.cfd.own(j, 1n+v)), (r3, rd))) == (Some{CronFileView.row_of(Cr.finish(p, c, o, j), 1n+v)}, (LCfd.cfd.own(Cr.finish(p, c, o, j), 1n+v), (r3, rd))) : CronFileView.Obs()}
      cfn.on_ow(cfn.owned(p, j), v, p, c, o, x, j, r3, rd, {==})

def cfn.fin_q(q: Bool, +v: Nat, +p: Nat, +c: Nat, +ji: Nat, +o: Cr.Out, +x: Nat, +dead: List<&2, Nat>, +rs: List<&2, Cr.Rec>, +r3: List<&2, Nat>, +rd: List<&2, Nat>, +eqq: {Nat.is_eq(x, ji) == q : Bool}) -> {(cfn.mrow(x, cfn.mhit(p, ji, LCfd.cfd.first(ji, rs)), LCfd.cfd.first(x, rs), 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), (cfn.mmarks(x, ji, p, LCfd.cfd.first(x, rs), 1n+v), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, LCfd.cfd.first(x, rs)), 1n+v), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, LCfd.cfd.first(x, rs)), 1n+v), (r3, rd))) : CronFileView.Obs()}:
  match q:
    case False{}:
      +u = {1n+v : Nat}
      +f = LCfd.cfd.first(x, rs)
      +kk = cfn.mhit(p, ji, LCfd.cfd.first(ji, rs))
      %cfn.rows_off(x, kk, f, u, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, u), cfn.names_hit_off(x, ji, p, LCfd.cfd.first(ji, rs), eqq)) : {(_, (cfn.mmarks(x, ji, p, f, u), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, f), u), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, f), u), (r3, rd))) : CronFileView.Obs()}
      %cfn.mm_off(x, ji, p, f, u, eqq) : {(LCfd.cfd.mrow(f, u), (_, (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, f), u), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, f), u), (r3, rd))) : CronFileView.Obs()}
      cfn.off_m(v, p, c, ji, o, x, dead, f, r3, rd, LCfd.cfd.first_id(x, rs), eqq)
    case True{}:
      %LCfl.cfl.eq_of(x, ji, eqq) : {(cfn.mrow(x, cfn.mhit(p, _, LCfd.cfd.first(_, rs)), LCfd.cfd.first(x, rs), 1n+v, Cron.ran_of(o), Cron.failed_of(o), Nat.mul(c, 1n+v)), (cfn.mmarks(x, _, p, LCfd.cfd.first(x, rs), 1n+v), (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.mapj(Cr.Finish{p, _, o}, c, dead, LCfd.cfd.first(x, rs)), 1n+v), (LCfd.cfd.mclaims(LCfd.cfd.mapj(Cr.Finish{p, _, o}, c, dead, LCfd.cfd.first(x, rs)), 1n+v), (r3, rd))) : CronFileView.Obs()}
      cfn.on_m(v, p, c, o, x, dead, LCfd.cfd.first(x, rs), r3, rd, LCfd.cfd.first_id(x, rs))

def CronFileView.cron_file_finish_refines(v, p, c, ji, o, x, dead, rs, rd, ok0):
  +ok = ok0
  +u = {1n+v : Nat}
  +cu = Nat.mul(c, u)
  +ro = Cron.ran_of(o)
  +fo = Cron.failed_of(o)
  +pp = CronFileView.pins_of(p, ji, rs)
  +ps = List.append(&2, CF.Pin, pp, CronFileView.unpinned(rd))
  +su = CronFile.stays_spec(CronFileView.unpinned(rd))
  +dp = CronFile.drops_spec(pp)
  +ms = CronFileView.marks_of(rs, u)
  +js = CronFileView.slots_of(rs, u)
  +kk = cfn.mhit(p, ji, LCfd.cfd.first(ji, rs))
  +rr = Cr.recs(Cr.Finish{p, ji, o}, c, dead, rs)
  +f = LCfd.cfd.first(x, rs)
  +r3 = CronFileView.raw_rows(CronFileView.rows_of(rs, u))
  -mr = cfn.mrow(x, kk, f, u, ro, fo, cu)
  -mk = cfn.mmarks(x, ji, p, f, u)
  +drr = Equal.trans(Bool, CronFileView.distinct(rr), CronFileView.distinct(rs), True{}, LCfd.cfd.distinct_recs(Cr.Finish{p, ji, o}, c, dead, rs), ok)
  %Equal.sym(Maybe<&2, Nat>, CronFile.hit_spec(ps), CronFile.hit_spec(pp), cfn.hit_app(pp, rd)) : {(CronFileView.row_at(x, CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, _, u, ro, fo, cu), u)), (CronFileView.marks_at(x, CronFileView.select_marks(ms, CronFile.drops_spec(ps))), (CronFileView.raw_rows(CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, _, u, ro, fo, cu), u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, CronFile.drops_spec(ps)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, Nat>, CronFile.hit_spec(pp), kk, cfn.hit(p, ji, rs, ok)) : {(CronFileView.row_at(x, CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, _, u, ro, fo, cu), u)), (CronFileView.marks_at(x, CronFileView.select_marks(ms, CronFile.drops_spec(ps))), (CronFileView.raw_rows(CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, _, u, ro, fo, cu), u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, CronFile.drops_spec(ps)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Bool>, CronFile.drops_spec(ps), List.append(&2, Bool, dp, su), cfn.drops_app(pp, rd)) : {(CronFileView.row_at(x, CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, kk, u, ro, fo, cu), u)), (CronFileView.marks_at(x, CronFileView.select_marks(ms, _)), (CronFileView.raw_rows(CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, kk, u, ro, fo, cu), u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, _))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, kk, u, ro, fo, cu), u)), mr, cfn.rows(x, rs, kk, u, ro, fo, cu)) : {(_, (CronFileView.marks_at(x, CronFileView.select_marks(ms, List.append(&2, Bool, dp, su))), (CronFileView.raw_rows(CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, kk, u, ro, fo, cu), u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, List.append(&2, Bool, dp, su)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.select_marks(ms, List.append(&2, Bool, dp, su))), mk, cfn.marks(x, p, ji, rs, su, u, ok)) : {(mr, (_, (CronFileView.raw_rows(CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, kk, u, ro, fo, cu), u)), CronFileView.select_raws(rd, CronFileView.after_marks(ms, List.append(&2, Bool, dp, su)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.finish_rows(rs, CronFile.finish_js_spec(js, kk, u, ro, fo, cu), u)), r3, cfn.raws(rs, CronFile.finish_js_spec(js, kk, u, ro, fo, cu), u)) : {(mr, (mk, (_, CronFileView.select_raws(rd, CronFileView.after_marks(ms, List.append(&2, Bool, dp, su)))))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Bool>, CronFileView.after_marks(ms, List.append(&2, Bool, dp, su)), su, cfn.after_drops(rs, p, ji, u, su)) : {(mr, (mk, (r3, CronFileView.select_raws(rd, _)))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.select_raws(rd, su), rd, cfn.raws_stay(rd)) : {(mr, (mk, (r3, _))) == (CronFileView.row_at(x, CronFileView.rows_of(rr, u)), (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, CronFileView.FRow>, CronFileView.row_at(x, CronFileView.rows_of(rr, u)), LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), LCfd.cfd.rows_at(x, rr, u)) : {(mr, (mk, (r3, rd))) == (_, (CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Cr.Claim>, CronFileView.marks_at(x, CronFileView.marks_of(rr, u)), LCfd.cfd.mclaims(LCfd.cfd.first(x, rr), u), LCfd.cfd.marks_at(x, rr, u, drr)) : {(mr, (mk, (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), (_, (CronFileView.raw_rows(CronFileView.rows_of(rr, u)), rd))) : CronFileView.Obs()}
  %Equal.sym(List<&2, Nat>, CronFileView.raw_rows(CronFileView.rows_of(rr, u)), r3, LCfd.cfd.raws_recs(Cr.Finish{p, ji, o}, c, dead, rs, u)) : {(mr, (mk, (r3, rd))) == (LCfd.cfd.mrow(LCfd.cfd.first(x, rr), u), (LCfd.cfd.mclaims(LCfd.cfd.first(x, rr), u), (_, rd))) : CronFileView.Obs()}
  %Equal.sym(Maybe<&2, Cr.Job>, LCfd.cfd.first(x, rr), LCfd.cfd.mapj(Cr.Finish{p, ji, o}, c, dead, f), LCfd.cfd.first_recs(Cr.Finish{p, ji, o}, c, dead, rs, x)) : {(mr, (mk, (r3, rd))) == (LCfd.cfd.mrow(_, u), (LCfd.cfd.mclaims(_, u), (r3, rd))) : CronFileView.Obs()}
  cfn.fin_q(Nat.is_eq(x, ji), v, p, c, ji, o, x, dead, rs, r3, rd, {==})
