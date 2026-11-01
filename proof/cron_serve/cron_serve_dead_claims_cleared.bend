# eukhe: the proof of LAW cron_serve_dead_claims_cleared
# A recovery answers every job record (kept as read, or the recovery's
# answer on a known one: render keeps them all) and every claim record
# (kept, or dropped when its verdict clears it): the claims rendered are
# the file's claims the verdict keeps (dc2.filt). A dead owner's claim is
# cleared (a live process's own claim is not a dead owner's); when the
# answer writes nothing, no claim was cleared, so none was a dead owner's.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ../../laws/cron_serve/safety.bend as CronServeSafety
import ./base/safety.bend as LSf
import ./base/logic.bend as LG

# the claims the verdicts keep
def dc2.fpick(+b: Bool, +c: CronServeSafety.SfC, +r: List<&2, CronServeSafety.SfC>) -> List<&2, CronServeSafety.SfC>:
  match b:
    case True{}:
      r
    case False{}:
      c <> r

def dc2.filt(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +cs: List<&2, CronServeSafety.SfC>) -> List<&2, CronServeSafety.SfC>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      dc2.fpick(Sv.clears(me, runs, dead, CronServeSafety.sf_pc(c)), c, dc2.filt(me, runs, dead, t))

# Rendering a recovery
# --------------------

def dc2.f1b(+b: Bool, +c: CronServeSafety.SfC, +t: List<&2, CronServeSafety.SfC>, +rct: List<&2, Sv.COut>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool, +r: List<&2, CronServeSafety.SfC>, +ih: {CronServeSafety.sf_render_c(rct, t, pjs, me, isc) == Some{r} : Maybe<&2, List<&2, CronServeSafety.SfC>>}) -> {CronServeSafety.sf_render_c(Sv.recover.claim(b) <> rct, c <> t, pjs, me, isc) == Some{dc2.fpick(b, c, r)} : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(rct, t, pjs, me, isc), Some{r}, ih) : {CronServeSafety.sf_cons(CronServeSafety.SfC, c, _) == Some{c <> r} : Maybe<&2, List<&2, CronServeSafety.SfC>>}
      {==}

def dc2.f1(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +isc: Bool) -> {CronServeSafety.sf_render_c(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs)), cs, pjs, me, isc) == Some{dc2.filt(me, runs, dead, cs)} : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      dc2.f1b(Sv.clears(me, runs, dead, CronServeSafety.sf_pc(c)), c, t, Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(t)), pjs, me, isc, dc2.filt(me, runs, dead, t), dc2.f1(me, runs, dead, t, pjs, isc))

def dc2.f4(+ids: List<&2, Nat>, +js: List<&2, CronServeSafety.SfJ>, +mk: Maybe<&2, CronServeSafety.SfJ>) -> {CronServeSafety.sf_render_j(Sv.recover.jobs(ids, CronServeSafety.sf_pjs(js)), js, mk) == Some{js} : Maybe<&2, List<&2, CronServeSafety.SfJ>>}:
  match js:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case CronServeSafety.SfJK{i, f}:
          %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfJ>>, CronServeSafety.sf_render_j(Sv.recover.jobs(ids, CronServeSafety.sf_pjs(t)), t, mk), Some{t}, dc2.f4(ids, t, mk)) : {CronServeSafety.sf_cons(CronServeSafety.SfJ, CronServeSafety.SfJK{i, f}, _) == Some{CronServeSafety.SfJK{i, f} <> t} : Maybe<&2, List<&2, CronServeSafety.SfJ>>}
          {==}
        case CronServeSafety.SfJR{y}:
          %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfJ>>, CronServeSafety.sf_render_j(Sv.recover.jobs(ids, CronServeSafety.sf_pjs(t)), t, mk), Some{t}, dc2.f4(ids, t, mk)) : {CronServeSafety.sf_cons(CronServeSafety.SfJ, CronServeSafety.SfJR{y}, _) == Some{CronServeSafety.SfJR{y} <> t} : Maybe<&2, List<&2, CronServeSafety.SfJ>>}
          {==}

# No dead owner's claim is kept
# -----------------------------

def dc2.k_own(+b: Bool, +d: String, +j: Nat, +o: Nat, +dead: List<&2, Nat>, +r: List<&2, CronServeSafety.SfC>, +ho: {Cr.has(o, dead) == False{} : Bool}, +ih: {CronServeSafety.sf_none_dead(r, dead) == True{} : Bool}) -> {CronServeSafety.sf_none_dead(dc2.fpick(Bool.not(b), CronServeSafety.SfCK{d, j, o}, r), dead) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Cr.has(o, dead), False{}, ho) : {Bool.and(Bool.not(_), CronServeSafety.sf_none_dead(r, dead)) == True{} : Bool}
      ih
    case False{}:
      ih

def dc2.k_th(+hb: Bool, +d: String, +j: Nat, +o: Nat, +dead: List<&2, Nat>, +r: List<&2, CronServeSafety.SfC>, +eh: {Cr.has(o, dead) == hb : Bool}, +ih: {CronServeSafety.sf_none_dead(r, dead) == True{} : Bool}) -> {CronServeSafety.sf_none_dead(dc2.fpick(hb, CronServeSafety.SfCK{d, j, o}, r), dead) == True{} : Bool}:
  match hb:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Cr.has(o, dead), False{}, eh) : {Bool.and(Bool.not(_), CronServeSafety.sf_none_dead(r, dead)) == True{} : Bool}
      ih

def dc2.k(+own: Bool, +me: Nat, +runs: List<&2, String>, +d: String, +j: Nat, +o: Nat, +dead: List<&2, Nat>, +r: List<&2, CronServeSafety.SfC>, +eo: {Nat.is_eq(o, me) == own : Bool}, +alive: {Cr.has(me, dead) == False{} : Bool}, +ih: {CronServeSafety.sf_none_dead(r, dead) == True{} : Bool}) -> {CronServeSafety.sf_none_dead(dc2.fpick(CS.clear(Sv.who(own, d, o, runs, dead)), CronServeSafety.SfCK{d, j, o}, r), dead) == True{} : Bool}:
  match own:
    case True{}:
      dc2.k_own(Sv.has_str(d, runs), d, j, o, dead, r, Equal.trans(Bool, Cr.has(o, dead), Cr.has(me, dead), False{}, Equal.cong(Nat, Bool, n => Cr.has(n, dead), o, me, LG.lg.eq_true(o, me, eo)), alive), ih)
    case False{}:
      dc2.k_th(Cr.has(o, dead), d, j, o, dead, r, {==}, ih)

def dc2.f2(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +cs: List<&2, CronServeSafety.SfC>, +alive: {Cr.has(me, dead) == False{} : Bool}) -> {CronServeSafety.sf_none_dead(dc2.filt(me, runs, dead, cs), dead) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{d, j, o}:
          dc2.k(Nat.is_eq(o, me), me, runs, d, j, o, dead, dc2.filt(me, runs, dead, t), {==}, alive, dc2.f2(me, runs, dead, t, alive))
        case CronServeSafety.SfCR{y}:
          dc2.f2(me, runs, dead, t, alive)

# A recovery that writes nothing cleared no claim
def dc2.f3b(+b: Bool, +c: CronServeSafety.SfC, +t: List<&2, CronServeSafety.SfC>, +r: List<&2, CronServeSafety.SfC>, +rct: List<&2, Sv.COut>, +h: {Sv.couts_move(Sv.recover.claim(b) <> rct) == False{} : Bool}, ih: {Sv.couts_move(rct) == False{} : Bool} -> {r == t : List<&2, CronServeSafety.SfC>}) -> {dc2.fpick(b, c, r) == c <> t : List<&2, CronServeSafety.SfC>}:
  match b:
    case True{}:
      LG.lg.tf({r == c <> t : List<&2, CronServeSafety.SfC>}, h)
    case False{}:
      Equal.cong(List<&2, CronServeSafety.SfC>, List<&2, CronServeSafety.SfC>, x => c <> x, r, t, ih(h))

def dc2.f3(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +cs: List<&2, CronServeSafety.SfC>, +h: {Sv.couts_move(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs))) == False{} : Bool}) -> {dc2.filt(me, runs, dead, cs) == cs : List<&2, CronServeSafety.SfC>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      dc2.f3b(Sv.clears(me, runs, dead, CronServeSafety.sf_pc(c)), c, t, dc2.filt(me, runs, dead, t), Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(t)), h, e => dc2.f3(me, runs, dead, t, e))

# The update
# ----------

def dc2.w(+wb: Bool, +js: List<&2, CronServeSafety.SfJ>, +cs: List<&2, CronServeSafety.SfC>, +me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +jm: Bool, +hw: {Bool.or(jm, Sv.couts_move(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs)))) == wb : Bool}, +alive: {Cr.has(me, dead) == False{} : Bool}) -> {CronServeSafety.sf_none_dead(CronServeSafety.sf_claims_of(CronServeSafety.sf_written(wb, False{}, CronServeSafety.SfRead{js, cs}, CronServeSafety.sf_render_j(Sv.recover.jobs(Sv.cleared(me, runs, dead, CronServeSafety.sf_pcs(cs)), CronServeSafety.sf_pjs(js)), js, None{}), CronServeSafety.sf_render_c(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs)), cs, CronServeSafety.sf_pjs(js), me, False{}))), dead) == True{} : Bool}:
  match wb:
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfJ>>, CronServeSafety.sf_render_j(Sv.recover.jobs(Sv.cleared(me, runs, dead, CronServeSafety.sf_pcs(cs)), CronServeSafety.sf_pjs(js)), js, None{}), Some{js}, dc2.f4(Sv.cleared(me, runs, dead, CronServeSafety.sf_pcs(cs)), js, None{})) : {CronServeSafety.sf_none_dead(CronServeSafety.sf_claims_of(CronServeSafety.sf_put(_, CronServeSafety.sf_render_c(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs)), cs, CronServeSafety.sf_pjs(js), me, False{}), CronServeSafety.SfRead{js, cs})), dead) == True{} : Bool}
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs)), cs, CronServeSafety.sf_pjs(js), me, False{}), Some{dc2.filt(me, runs, dead, cs)}, dc2.f1(me, runs, dead, cs, CronServeSafety.sf_pjs(js), False{})) : {CronServeSafety.sf_none_dead(CronServeSafety.sf_claims_of(CronServeSafety.sf_put(Some{js}, _, CronServeSafety.SfRead{js, cs})), dead) == True{} : Bool}
      dc2.f2(me, runs, dead, cs, alive)
    case False{}:
      %dc2.f3(me, runs, dead, cs, LSf.sg.or_fr(jm, Sv.couts_move(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs))), hw)) : {CronServeSafety.sf_none_dead(_, dead) == True{} : Bool}
      dc2.f2(me, runs, dead, cs, alive)

def dc2.main(+f: CronServeSafety.SfFile, +me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +alive: {Cr.has(me, dead) == False{} : Bool}) -> {CronServeSafety.sf_none_dead(CronServeSafety.sf_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(CronServe.sv_reply(Sv.go(runs, me, LSf.sg.torn(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_pcs(CronServeSafety.sf_claims_of(f)), Sv.ORecover{dead}))), CronServe.sv_aside(CronServe.sv_reply(Sv.go(runs, me, LSf.sg.torn(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_pcs(CronServeSafety.sf_claims_of(f)), Sv.ORecover{dead}))), f, CronServeSafety.sf_render_j(CronServe.sv_jobs(CronServe.sv_reply(Sv.go(runs, me, LSf.sg.torn(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_pcs(CronServeSafety.sf_claims_of(f)), Sv.ORecover{dead}))), CronServeSafety.sf_jobs(f), None{}), CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.go(runs, me, LSf.sg.torn(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_pcs(CronServeSafety.sf_claims_of(f)), Sv.ORecover{dead}))), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), me, False{})), dead, CronServeSafety.sf_moved(CronServe.sv_aside(CronServe.sv_reply(Sv.go(runs, me, LSf.sg.torn(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_pcs(CronServeSafety.sf_claims_of(f)), Sv.ORecover{dead}))), f, aside)}), dead) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      {==}
    case CronServeSafety.SfTorn{t}:
      {==}
    case CronServeSafety.SfRead{js, cs}:
      dc2.w(Bool.or(Sv.jouts_move(Sv.recover.jobs(Sv.cleared(me, runs, dead, CronServeSafety.sf_pcs(cs)), CronServeSafety.sf_pjs(js))), Sv.couts_move(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs)))), js, cs, me, runs, dead, Sv.jouts_move(Sv.recover.jobs(Sv.cleared(me, runs, dead, CronServeSafety.sf_pcs(cs)), CronServeSafety.sf_pjs(js))), {==}, alive)

def CronServeSafety.cron_serve_dead_claims_cleared(w, p, runs, x, alive):
  match w:
    case CronServeSafety.SfWorld{+f, +dead, +aside}:
      +op2 = {Sv.ORecover{dead} : Sv.Op}
      +r = CronServe.sv_reply(Sv.serve(runs, p, CronServeSafety.sf_disk(f), op2))
      %Equal.sym(CronServeSafety.SfWorld, CronServeSafety.sf_apply(r, f, op2, p, dead, aside), CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), CronServe.sv_aside(r), f, CronServeSafety.sf_render_j(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), None{}), CronServeSafety.sf_render_c(CronServe.sv_claims_out(r), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, False{})), dead, CronServeSafety.sf_moved(CronServe.sv_aside(r), f, aside)}, LSf.sg.up(r, f, op2, p, dead, aside)) : {CronServeSafety.sf_none_dead(CronServeSafety.sf_claims(_), dead) == True{} : Bool}
      %Equal.sym(Sv.Served, Sv.serve(runs, p, CronServeSafety.sf_disk(f), op2), Sv.go(runs, p, LSf.sg.torn(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_pcs(CronServeSafety.sf_claims_of(f)), op2), LSf.sg.serve_go(runs, p, f, op2)) : {CronServeSafety.sf_none_dead(CronServeSafety.sf_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(CronServe.sv_reply(_)), CronServe.sv_aside(CronServe.sv_reply(_)), f, CronServeSafety.sf_render_j(CronServe.sv_jobs(CronServe.sv_reply(_)), CronServeSafety.sf_jobs(f), None{}), CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(_)), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, False{})), dead, CronServeSafety.sf_moved(CronServe.sv_aside(CronServe.sv_reply(_)), f, aside)}), dead) == True{} : Bool}
      dc2.main(f, p, runs, dead, aside, alive)
