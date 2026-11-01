# eukhe: the proof of LAW cron_serve_corrupt_kept
# An update moves the file aside exactly when it is unreadable
# (LSf.sg.aside_f): a corrupt file's bytes go to the files moved aside, and
# whatever is written after is not corrupt; the files moved aside only
# grow. Other writers leave a corrupt file as it is.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ../../laws/cron_serve/safety.bend as CronServeSafety
import ./base/safety.bend as LSf
import ./base/logic.bend as LG

def ck.b0(+t: Nat, +g: CronServeSafety.SfFile, +dead: List<&2, Nat>, +a2: List<&2, Nat>, +nt: {LSf.sg.torn(g) == False{} : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{g, dead, a2}) == Cr.has(t, a2) : Bool}:
  match g:
    case CronServeSafety.SfMissing{}:
      {==}
    case CronServeSafety.SfTorn{x}:
      LG.lg.tf({CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.SfTorn{x}, dead, a2}) == Cr.has(t, a2) : Bool}, nt)
    case CronServeSafety.SfRead{js, cs}:
      {==}

def ck.put(+t: Nat, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +mc: Maybe<&2, List<&2, CronServeSafety.SfC>>, +b: CronServeSafety.SfFile, +dead: List<&2, Nat>, +a2: List<&2, Nat>, +hb: {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{b, dead, a2}) == Cr.has(t, a2) : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_put(mj, mc, b), dead, a2}) == Cr.has(t, a2) : Bool}:
  match mj:
    case None{}:
      hb
    case Some{js}:
      match mc:
        case None{}:
          hb
        case Some{cs}:
          {==}

# what an update writes over a file that is not corrupt after the move is
# not corrupt
def ck.written(+t: Nat, +w: Bool, +a: Bool, +f: CronServeSafety.SfFile, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +mc: Maybe<&2, List<&2, CronServeSafety.SfC>>, +dead: List<&2, Nat>, +a2: List<&2, Nat>, +nb: {LSf.sg.torn(CronServeSafety.sf_base(a, f)) == False{} : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_written(w, a, f, mj, mc), dead, a2}) == Cr.has(t, a2) : Bool}:
  match w:
    case True{}:
      ck.put(t, mj, mc, CronServeSafety.sf_base(a, f), dead, a2, ck.b0(t, CronServeSafety.sf_base(a, f), dead, a2, nb))
    case False{}:
      ck.b0(t, CronServeSafety.sf_base(a, f), dead, a2, nb)

# an update, its file moved aside exactly when it is unreadable
def ck.up(+f: CronServeSafety.SfFile, +t: Nat, +w: Bool, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +mc: Maybe<&2, List<&2, CronServeSafety.SfC>>, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +kept: {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{f, dead, aside}) == True{} : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_written(w, LSf.sg.torn(f), f, mj, mc), dead, CronServeSafety.sf_moved(LSf.sg.torn(f), f, aside)}) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      Equal.trans(Bool, CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_written(w, False{}, CronServeSafety.SfMissing{}, mj, mc), dead, aside}), Cr.has(t, aside), True{}, ck.written(t, w, False{}, CronServeSafety.SfMissing{}, mj, mc, dead, aside, {==}), kept)
    case CronServeSafety.SfTorn{+x}:
      Equal.trans(Bool, CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_written(w, True{}, CronServeSafety.SfTorn{x}, mj, mc), dead, x <> aside}), Cr.has(t, x <> aside), True{}, ck.written(t, w, True{}, CronServeSafety.SfTorn{x}, mj, mc, dead, x <> aside, {==}), kept)
    case CronServeSafety.SfRead{+js, +cs}:
      Equal.trans(Bool, CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_written(w, False{}, CronServeSafety.SfRead{js, cs}, mj, mc), dead, aside}), Cr.has(t, aside), True{}, ck.written(t, w, False{}, CronServeSafety.SfRead{js, cs}, mj, mc, dead, aside, {==}), kept)

# Other events
# ------------

def ck.die(+f: CronServeSafety.SfFile, +t: Nat, +p: Nat, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +kept: {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{f, dead, aside}) == True{} : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{f, p <> dead, aside}) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      kept
    case CronServeSafety.SfTorn{x}:
      kept
    case CronServeSafety.SfRead{js, cs}:
      kept

def ck.rj(+f: CronServeSafety.SfFile, +t: Nat, +x: Nat, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +kept: {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{f, dead, aside}) == True{} : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_add_job(x, f), dead, aside}) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      kept
    case CronServeSafety.SfTorn{y}:
      kept
    case CronServeSafety.SfRead{js, cs}:
      kept

def ck.rc(+f: CronServeSafety.SfFile, +t: Nat, +x: Nat, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +kept: {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{f, dead, aside}) == True{} : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_add_claim(x, f), dead, aside}) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      kept
    case CronServeSafety.SfTorn{y}:
      kept
    case CronServeSafety.SfRead{js, cs}:
      kept

def ck.fa(+f: CronServeSafety.SfFile, +t: Nat, +k: Nat, +g: CS.Fact, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +kept: {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{f, dead, aside}) == True{} : Bool}) -> {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_facts(k, g, f), dead, aside}) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      kept
    case CronServeSafety.SfTorn{y}:
      kept
    case CronServeSafety.SfRead{js, cs}:
      kept

def CronServeSafety.cron_serve_corrupt_kept(w, e, t, nc, kept):
  match w:
    case CronServeSafety.SfWorld{+f, +dead, +aside}:
      match e:
        case CronServeSafety.SfUp{+p, +runs, +op}:
          +op2 = CronServeSafety.sf_op(op, dead)
          +r = CronServe.sv_reply(Sv.serve(runs, p, CronServeSafety.sf_disk(f), op2))
          %Equal.sym(CronServeSafety.SfWorld, CronServeSafety.sf_apply(r, f, op2, p, dead, aside), CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), CronServe.sv_aside(r), f, CronServeSafety.sf_render_j(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2)), CronServeSafety.sf_render_c(CronServe.sv_claims_out(r), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2))), dead, CronServeSafety.sf_moved(CronServe.sv_aside(r), f, aside)}, LSf.sg.up(r, f, op2, p, dead, aside)) : {CronServeSafety.sf_keeps_torn(t, _) == True{} : Bool}
          %Equal.sym(Bool, CronServe.sv_aside(r), LSf.sg.torn(f), LSf.sg.aside_f(runs, p, f, op2)) : {CronServeSafety.sf_keeps_torn(t, CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), _, f, CronServeSafety.sf_render_j(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2)), CronServeSafety.sf_render_c(CronServe.sv_claims_out(r), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2))), dead, CronServeSafety.sf_moved(_, f, aside)}) == True{} : Bool}
          ck.up(f, t, CronServe.sv_write(r), CronServeSafety.sf_render_j(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2)), CronServeSafety.sf_render_c(CronServe.sv_claims_out(r), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2)), dead, aside, kept)
        case CronServeSafety.SfDie{+q}:
          ck.die(f, t, q, dead, aside, kept)
        case CronServeSafety.SfRawJob{+x}:
          ck.rj(f, t, x, dead, aside, kept)
        case CronServeSafety.SfRawClaim{+x}:
          ck.rc(f, t, x, dead, aside, kept)
        case CronServeSafety.SfFacts{+k, +g}:
          ck.fa(f, t, k, g, dead, aside, kept)
        case CronServeSafety.SfCorrupt{x}:
          LG.lg.tf({CronServeSafety.sf_keeps_torn(t, CronServeSafety.sf_step(CronServeSafety.SfWorld{f, dead, aside}, CronServeSafety.SfCorrupt{x})) == True{} : Bool}, nc)
