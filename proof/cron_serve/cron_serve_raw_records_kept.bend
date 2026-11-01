# eukhe: the proof of LAW cron_serve_raw_records_kept
# A rendered answer keeps every job record this build cannot read in its
# place (render refuses any answer on one but kept-as-read) and adds only
# known records; every claim record it cannot read is answered kept
# (cron_serve_records_in_place), so it stays. A file that is not written
# stays; an unreadable or missing file has no records. Other writers add
# one record last, or change a known job's facts.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ../../laws/cron_serve/safety.bend as CronServeSafety
import ./base/safety.bend as LSf
import ./base/logic.bend as LG

# Prefixes
# --------

def rk.refl(+xs: List<&2, Nat>) -> {CronServeSafety.sf_prefix(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      LG.lg.and_t(Nat.is_eq(x, x), CronServeSafety.sf_prefix(t, t), LG.lg.eq_refl(x), rk.refl(t))

def rk.snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# a job's bytes, once more at the end
def rk.sj(+js: List<&2, CronServeSafety.SfJ>, +x: Nat) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(js), CronServeSafety.sf_raw_jobs.of(List.append(&2, CronServeSafety.SfJ, js, [CronServeSafety.SfJR{x}]))) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case CronServeSafety.SfJK{i, f}:
          rk.sj(t, x)
        case CronServeSafety.SfJR{+y}:
          LG.lg.and_t(Nat.is_eq(y, y), CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(t), CronServeSafety.sf_raw_jobs.of(List.append(&2, CronServeSafety.SfJ, t, [CronServeSafety.SfJR{x}]))), LG.lg.eq_refl(y), rk.sj(t, x))

def rk.sc(+cs: List<&2, CronServeSafety.SfC>, +x: Nat) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(cs), CronServeSafety.sf_raw_claims.of(List.append(&2, CronServeSafety.SfC, cs, [CronServeSafety.SfCR{x}]))) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{d, j, o}:
          rk.sc(t, x)
        case CronServeSafety.SfCR{+y}:
          LG.lg.and_t(Nat.is_eq(y, y), CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(t), CronServeSafety.sf_raw_claims.of(List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCR{x}]))), LG.lg.eq_refl(y), rk.sc(t, x))

# a job's facts changed
def rk.sf(+k: Nat, +g: CS.Fact, +js: List<&2, CronServeSafety.SfJ>) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(js), CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_set_fact(k, g, js))) == True{} : Bool}:
  match k js:
    case _ Nil{}:
      {==}
    case 0n r <> t:
      match r:
        case CronServeSafety.SfJK{i, f}:
          rk.refl(CronServeSafety.sf_raw_jobs.of(t))
        case CronServeSafety.SfJR{x}:
          rk.refl(x <> CronServeSafety.sf_raw_jobs.of(t))
    case 1n+p r <> t:
      match r:
        case CronServeSafety.SfJK{i, f}:
          rk.sf(p, g, t)
        case CronServeSafety.SfJR{+y}:
          LG.lg.and_t(Nat.is_eq(y, y), CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(t), CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_set_fact(p, g, t))), LG.lg.eq_refl(y), rk.sf(p, g, t))

# Rendering
# ---------

def rk.pj(+r: List<&2, Nat>, +m: Maybe<&2, List<&2, CronServeSafety.SfJ>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ys}:
      CronServeSafety.sf_prefix(r, CronServeSafety.sf_raw_jobs.of(ys))

def rk.pc(+r: List<&2, Nat>, +m: Maybe<&2, List<&2, CronServeSafety.SfC>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ys}:
      CronServeSafety.sf_prefix(r, CronServeSafety.sf_raw_claims.of(ys))

def rk.nil_j(+m: Maybe<&2, List<&2, CronServeSafety.SfJ>>) -> {rk.pj(Nil{}, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{ys}:
      {==}

def rk.nil_c(+m: Maybe<&2, List<&2, CronServeSafety.SfC>>) -> {rk.pc(Nil{}, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{ys}:
      {==}

def rk.cj(+m: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +x: CronServeSafety.SfJ, +t: List<&2, CronServeSafety.SfJ>, +ih: {rk.pj(CronServeSafety.sf_raw_jobs.of(t), m) == True{} : Bool}) -> {rk.pj(CronServeSafety.sf_raw_jobs.of(x <> t), CronServeSafety.sf_cons(CronServeSafety.SfJ, x, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{ys}:
      match x:
        case CronServeSafety.SfJK{i, f}:
          ih
        case CronServeSafety.SfJR{y}:
          LG.lg.and_t(Nat.is_eq(y, y), CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(t), CronServeSafety.sf_raw_jobs.of(ys)), LG.lg.eq_refl(y), ih)

def rk.aj(+x: CronServeSafety.SfJ, +m: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +t: List<&2, CronServeSafety.SfJ>, +ih: {rk.pj(CronServeSafety.sf_raw_jobs.of(t), m) == True{} : Bool}) -> {rk.pj(CronServeSafety.sf_raw_jobs.of(x <> t), CronServeSafety.sf_rj.answer(x, m)) == True{} : Bool}:
  match x:
    case CronServeSafety.SfJK{i, f}:
      rk.cj(m, CronServeSafety.SfJK{i, f}, t, ih)
    case CronServeSafety.SfJR{y}:
      {==}

# a rendered answer keeps the job records this build cannot read
def rk.rj(+jo: List<&2, Sv.JOut>, +js: List<&2, CronServeSafety.SfJ>, +mk: Maybe<&2, CronServeSafety.SfJ>) -> {rk.pj(CronServeSafety.sf_raw_jobs.of(js), CronServeSafety.sf_render_j(jo, js, mk)) == True{} : Bool}:
  match jo:
    case Nil{}:
      match js:
        case Nil{}:
          {==}
        case x <> t:
          {==}
    case o <> ot:
      match o:
        case Sv.JSame{}:
          match js:
            case Nil{}:
              {==}
            case x <> t:
              rk.cj(CronServeSafety.sf_render_j(ot, t, mk), x, t, rk.rj(ot, t, mk))
        case Sv.JNew{}:
          match js:
            case Nil{}:
              rk.nil_j(CronServeSafety.sf_rj.made(mk, CronServeSafety.sf_render_j(ot, Nil{}, mk)))
            case x <> t:
              {==}
        case Sv.JTook{y}:
          match js:
            case Nil{}:
              {==}
            case x <> t:
              rk.aj(x, CronServeSafety.sf_render_j(ot, t, mk), t, rk.rj(ot, t, mk))
        case Sv.JBack{y}:
          match js:
            case Nil{}:
              {==}
            case x <> t:
              rk.aj(x, CronServeSafety.sf_render_j(ot, t, mk), t, rk.rj(ot, t, mk))
        case Sv.JFin{y}:
          match js:
            case Nil{}:
              {==}
            case x <> t:
              rk.aj(x, CronServeSafety.sf_render_j(ot, t, mk), t, rk.rj(ot, t, mk))
        case Sv.JCut{y}:
          match js:
            case Nil{}:
              {==}
            case x <> t:
              rk.aj(x, CronServeSafety.sf_render_j(ot, t, mk), t, rk.rj(ot, t, mk))
        case Sv.JAgain{y}:
          match js:
            case Nil{}:
              {==}
            case x <> t:
              rk.aj(x, CronServeSafety.sf_render_j(ot, t, mk), t, rk.rj(ot, t, mk))

def rk.cc(+m: Maybe<&2, List<&2, CronServeSafety.SfC>>, +c: CronServeSafety.SfC, +t: List<&2, CronServeSafety.SfC>, +ih: {rk.pc(CronServeSafety.sf_raw_claims.of(t), m) == True{} : Bool}) -> {rk.pc(CronServeSafety.sf_raw_claims.of(c <> t), CronServeSafety.sf_cons(CronServeSafety.SfC, c, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{ys}:
      match c:
        case CronServeSafety.SfCK{d, j, o}:
          ih
        case CronServeSafety.SfCR{y}:
          LG.lg.and_t(Nat.is_eq(y, y), CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(t), CronServeSafety.sf_raw_claims.of(ys)), LG.lg.eq_refl(y), ih)

def rk.keep_placed(+c: CronServeSafety.SfC, +cs: List<&2, Sv.CRec>, +co: List<&2, Sv.COut>, +h: {CronServe.sv_claims_placed(CronServeSafety.sf_pc(c) <> cs, Sv.CKeep{} <> co) == True{} : Bool}) -> {CronServe.sv_claims_placed(cs, co) == True{} : Bool}:
  match c:
    case CronServeSafety.SfCK{d, j, o}:
      h
    case CronServeSafety.SfCR{y}:
      h

def rk.new_placed(+c: CronServeSafety.SfC, +cs: List<&2, Sv.CRec>, +k: Nat, +d: String, +co: List<&2, Sv.COut>, -G: Type, +h: {CronServe.sv_claims_placed(CronServeSafety.sf_pc(c) <> cs, Sv.CNew{k, d} <> co) == True{} : Bool}) -> G:
  match c:
    case CronServeSafety.SfCK{x, j, o}:
      LG.lg.ft(G, h)
    case CronServeSafety.SfCR{y}:
      LG.lg.ft(G, h)

# a rendered answer that keeps every claim record this build cannot read
# keeps them
def rk.rc(+co: List<&2, Sv.COut>, +cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool, +placed: {CronServe.sv_claims_placed(CronServeSafety.sf_pcs(cs), co) == True{} : Bool}) -> {rk.pc(CronServeSafety.sf_raw_claims.of(cs), CronServeSafety.sf_render_c(co, cs, pjs, me, isc)) == True{} : Bool}:
  match co:
    case Nil{}:
      match cs:
        case Nil{}:
          {==}
        case c <> t:
          {==}
    case o <> ot:
      match o:
        case Sv.CKeep{}:
          match cs:
            case Nil{}:
              {==}
            case c <> t:
              rk.cc(CronServeSafety.sf_render_c(ot, t, pjs, me, isc), c, t, rk.rc(ot, t, pjs, me, isc, rk.keep_placed(c, CronServeSafety.sf_pcs(t), ot, placed)))
        case Sv.CDrop{}:
          match cs:
            case Nil{}:
              {==}
            case c <> t:
              match c:
                case CronServeSafety.SfCK{d, j, w}:
                  rk.rc(ot, t, pjs, me, isc, placed)
                case CronServeSafety.SfCR{y}:
                  LG.lg.ft({rk.pc(CronServeSafety.sf_raw_claims.of(CronServeSafety.SfCR{y} <> t), CronServeSafety.sf_render_c(Sv.CDrop{} <> ot, CronServeSafety.SfCR{y} <> t, pjs, me, isc)) == True{} : Bool}, placed)
        case Sv.CNew{k, d}:
          match cs:
            case Nil{}:
              rk.nil_c(CronServeSafety.sf_render_c(Sv.CNew{k, d} <> ot, Nil{}, pjs, me, isc))
            case c <> t:
              rk.new_placed(c, CronServeSafety.sf_pcs(t), k, d, ot, {rk.pc(CronServeSafety.sf_raw_claims.of(c <> t), CronServeSafety.sf_render_c(Sv.CNew{k, d} <> ot, c <> t, pjs, me, isc)) == True{} : Bool}, placed)

# The update
# ----------

def rk.wr(+w: Bool, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +mc: Maybe<&2, List<&2, CronServeSafety.SfC>>, +js: List<&2, CronServeSafety.SfJ>, +cs: List<&2, CronServeSafety.SfC>, +dead: List<&2, Nat>, +a2: List<&2, Nat>, +hj: {rk.pj(CronServeSafety.sf_raw_jobs.of(js), mj) == True{} : Bool}, +hc: {rk.pc(CronServeSafety.sf_raw_claims.of(cs), mc) == True{} : Bool}) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(js), CronServeSafety.sf_raw_jobs(CronServeSafety.SfWorld{CronServeSafety.sf_written(w, False{}, CronServeSafety.SfRead{js, cs}, mj, mc), dead, a2})) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(cs), CronServeSafety.sf_raw_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(w, False{}, CronServeSafety.SfRead{js, cs}, mj, mc), dead, a2})) == True{} : Bool}:
  match w:
    case False{}:
      (rk.refl(CronServeSafety.sf_raw_jobs.of(js)), rk.refl(CronServeSafety.sf_raw_claims.of(cs)))
    case True{}:
      match mj:
        case None{}:
          (rk.refl(CronServeSafety.sf_raw_jobs.of(js)), rk.refl(CronServeSafety.sf_raw_claims.of(cs)))
        case Some{js2}:
          match mc:
            case None{}:
              (rk.refl(CronServeSafety.sf_raw_jobs.of(js)), rk.refl(CronServeSafety.sf_raw_claims.of(cs)))
            case Some{cs2}:
              (hj, hc)

def rk.hc(+f: CronServeSafety.SfFile, +runs: List<&2, String>, +p: Nat, +op: Sv.Op) -> {rk.pc(CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(f)), CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, CronServeSafety.sf_disk(f), op))), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      rk.nil_c(CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Missing{}, op))), Nil{}, Nil{}, p, CronServeSafety.sf_isc(op)))
    case CronServeSafety.SfTorn{t}:
      rk.nil_c(CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Torn{}, op))), Nil{}, Nil{}, p, CronServeSafety.sf_isc(op)))
    case CronServeSafety.SfRead{js, cs}:
      rk.rc(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs)}, op))), cs, CronServeSafety.sf_pjs(js), p, CronServeSafety.sf_isc(op), rk.snd({CronServe.sv_jobs_placed(CronServeSafety.sf_pjs(js), CronServe.sv_jobs(CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs)}, op))), CronServe.sv_is_create(op)) == True{} : Bool}, {CronServe.sv_claims_placed(CronServeSafety.sf_pcs(cs), CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs)}, op)))) == True{} : Bool}, CronServe.cron_serve_records_in_place(runs, p, CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs), op)))

def rk.up(+f: CronServeSafety.SfFile, +w: Bool, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +mc: Maybe<&2, List<&2, CronServeSafety.SfC>>, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +hj: {rk.pj(CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(f)), mj) == True{} : Bool}, +hc: {rk.pc(CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(f)), mc) == True{} : Bool}) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_raw_jobs(CronServeSafety.SfWorld{CronServeSafety.sf_written(w, LSf.sg.torn(f), f, mj, mc), dead, CronServeSafety.sf_moved(LSf.sg.torn(f), f, aside)})) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(f)), CronServeSafety.sf_raw_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(w, LSf.sg.torn(f), f, mj, mc), dead, CronServeSafety.sf_moved(LSf.sg.torn(f), f, aside)})) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      ({==}, {==})
    case CronServeSafety.SfTorn{t}:
      ({==}, {==})
    case CronServeSafety.SfRead{js, cs}:
      rk.wr(w, mj, mc, js, cs, dead, aside, hj, hc)

# Other events
# ------------

def rk.addj(+f: CronServeSafety.SfFile, +x: Nat) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(CronServeSafety.sf_add_job(x, f)))) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(f)), CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(CronServeSafety.sf_add_job(x, f)))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      ({==}, {==})
    case CronServeSafety.SfTorn{t}:
      ({==}, {==})
    case CronServeSafety.SfRead{js, cs}:
      (rk.sj(js, x), rk.refl(CronServeSafety.sf_raw_claims.of(cs)))

def rk.addc(+f: CronServeSafety.SfFile, +x: Nat) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(CronServeSafety.sf_add_claim(x, f)))) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(f)), CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(CronServeSafety.sf_add_claim(x, f)))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      ({==}, {==})
    case CronServeSafety.SfTorn{t}:
      ({==}, {==})
    case CronServeSafety.SfRead{js, cs}:
      (rk.refl(CronServeSafety.sf_raw_jobs.of(js)), rk.sc(cs, x))

def rk.fa(+f: CronServeSafety.SfFile, +k: Nat, +g: CS.Fact) -> {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(CronServeSafety.sf_facts(k, g, f)))) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(f)), CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(CronServeSafety.sf_facts(k, g, f)))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      ({==}, {==})
    case CronServeSafety.SfTorn{t}:
      ({==}, {==})
    case CronServeSafety.SfRead{js, cs}:
      (rk.sf(k, g, js), rk.refl(CronServeSafety.sf_raw_claims.of(cs)))

def CronServeSafety.cron_serve_raw_records_kept(w, e, nc):
  match w:
    case CronServeSafety.SfWorld{+f, +dead, +aside}:
      match e:
        case CronServeSafety.SfUp{+p, +runs, +op}:
          +op2 = CronServeSafety.sf_op(op, dead)
          +r = CronServe.sv_reply(Sv.serve(runs, p, CronServeSafety.sf_disk(f), op2))
          +mj = CronServeSafety.sf_render_j(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2))
          +mc = CronServeSafety.sf_render_c(CronServe.sv_claims_out(r), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2))
          %Equal.sym(CronServeSafety.SfWorld, CronServeSafety.sf_apply(r, f, op2, p, dead, aside), CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), CronServe.sv_aside(r), f, mj, mc), dead, CronServeSafety.sf_moved(CronServe.sv_aside(r), f, aside)}, LSf.sg.up(r, f, op2, p, dead, aside)) : {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs(CronServeSafety.SfWorld{f, dead, aside}), CronServeSafety.sf_raw_jobs(_)) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims(CronServeSafety.SfWorld{f, dead, aside}), CronServeSafety.sf_raw_claims(_)) == True{} : Bool}
          %Equal.sym(Bool, CronServe.sv_aside(r), LSf.sg.torn(f), LSf.sg.aside_f(runs, p, f, op2)) : {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs(CronServeSafety.SfWorld{f, dead, aside}), CronServeSafety.sf_raw_jobs(CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), _, f, mj, mc), dead, CronServeSafety.sf_moved(_, f, aside)})) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims(CronServeSafety.SfWorld{f, dead, aside}), CronServeSafety.sf_raw_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), _, f, mj, mc), dead, CronServeSafety.sf_moved(_, f, aside)})) == True{} : Bool}
          rk.up(f, CronServe.sv_write(r), mj, mc, dead, aside, rk.rj(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2)), rk.hc(f, runs, p, op2))
        case CronServeSafety.SfDie{q}:
          (rk.refl(CronServeSafety.sf_raw_jobs.of(CronServeSafety.sf_jobs(f))), rk.refl(CronServeSafety.sf_raw_claims.of(CronServeSafety.sf_claims_of(f))))
        case CronServeSafety.SfRawJob{+x}:
          rk.addj(f, x)
        case CronServeSafety.SfRawClaim{+x}:
          rk.addc(f, x)
        case CronServeSafety.SfFacts{+k, +g}:
          rk.fa(f, k, g)
        case CronServeSafety.SfCorrupt{x}:
          LG.lg.tf({CronServeSafety.sf_prefix(CronServeSafety.sf_raw_jobs(CronServeSafety.SfWorld{f, dead, aside}), CronServeSafety.sf_raw_jobs(CronServeSafety.sf_step(CronServeSafety.SfWorld{f, dead, aside}, CronServeSafety.SfCorrupt{x}))) == True{} : Bool} & {CronServeSafety.sf_prefix(CronServeSafety.sf_raw_claims(CronServeSafety.SfWorld{f, dead, aside}), CronServeSafety.sf_raw_claims(CronServeSafety.sf_step(CronServeSafety.SfWorld{f, dead, aside}, CronServeSafety.SfCorrupt{x}))) == True{} : Bool}, nc)
