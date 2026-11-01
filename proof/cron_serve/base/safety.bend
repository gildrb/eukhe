# eukhe: lemmas the proofs of laws/cron_serve/safety.bend share: an update
# is the serve on the records the file holds (none when it is missing or
# unreadable); the world after an update, field by field; the answer moves
# the file aside exactly when it is unreadable; Bool and Nat facts.

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/cron_serve.bend as Sv
import ../../../laws/cron_serve/serve.bend as CronServe
import ../../../laws/cron_serve/safety.bend as Sf
import ./logic.bend as LG

# The update
# ----------

# the file is unreadable
def sg.torn(f: Sf.SfFile) -> Bool:
  match f:
    case Sf.SfMissing{}:
      False{}
    case Sf.SfTorn{t}:
      True{}
    case Sf.SfRead{js, cs}:
      False{}

def sg.serve_go(+runs: List<&2, String>, +me: Nat, f: Sf.SfFile, +op: Sv.Op) -> {Sv.serve(runs, me, Sf.sf_disk(f), op) == Sv.go(runs, me, sg.torn(f), Sf.sf_pjs(Sf.sf_jobs(f)), Sf.sf_pcs(Sf.sf_claims_of(f)), op) : Sv.Served}:
  match f:
    case Sf.SfMissing{}:
      {==}
    case Sf.SfTorn{t}:
      {==}
    case Sf.SfRead{js, cs}:
      {==}

# the world after an update, field by field
def sg.up(o: Sv.Out, +f: Sf.SfFile, +op: Sv.Op, +me: Nat, dead: List<&2, Nat>, aside: List<&2, Nat>) -> {Sf.sf_apply(o, f, op, me, dead, aside) == Sf.SfWorld{Sf.sf_written(CronServe.sv_write(o), CronServe.sv_aside(o), f, Sf.sf_render_j(CronServe.sv_jobs(o), Sf.sf_jobs(f), Sf.sf_made(op)), Sf.sf_render_c(CronServe.sv_claims_out(o), Sf.sf_claims_of(f), Sf.sf_pjs(Sf.sf_jobs(f)), me, Sf.sf_isc(op))), dead, Sf.sf_moved(CronServe.sv_aside(o), f, aside)} : Sf.SfWorld}:
  match o:
    case Sv.Out{a, w, jo, co}:
      {==}

# Moving aside
# ------------

def sg.aside_ce(a: Bool, +runs: List<&2, String>, cs: List<&2, Sv.CRec>, p: Sv.Pass) -> {CronServe.sv_aside(CronServe.sv_reply(Sv.claim.end(a, runs, cs, p))) == a : Bool}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      {==}

def sg.aside_own(own: Bool, a: Bool, +j: Nat, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {CronServe.sv_aside(Sv.finish.own(own, a, j, d, ran, failed, now, js, cs)) == a : Bool}:
  match own:
    case True{}:
      {==}
    case False{}:
      {==}

def sg.aside_found(m: Maybe<&2, Sv.Hit>, +me: Nat, a: Bool, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {CronServe.sv_aside(Sv.finish.found(m, me, a, d, ran, failed, now, js, cs)) == a : Bool}:
  match m:
    case None{}:
      {==}
    case Some{h}:
      match h:
        case Sv.Hit{j, +o}:
          sg.aside_own(Nat.is_eq(o, me), a, j, d, ran, failed, now, js, cs)

def sg.aside_fin(b: Bool, +me: Nat, +runs: List<&2, String>, a: Bool, +d: String, ran: Bool, failed: Bool, now: Nat, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>) -> {CronServe.sv_aside(CronServe.sv_reply(Sv.finish(b, me, runs, a, d, ran, failed, now, js, cs))) == a : Bool}:
  match b:
    case True{}:
      sg.aside_found(Sv.claim_of(d, cs), me, a, d, ran, failed, now, js, cs)
    case False{}:
      {==}

# an update moves the file aside exactly when the file is unreadable
def sg.aside_go(+runs: List<&2, String>, +me: Nat, a: Bool, +js: List<&2, Sv.JRec>, +cs: List<&2, Sv.CRec>, op: Sv.Op) -> {CronServe.sv_aside(CronServe.sv_reply(Sv.go(runs, me, a, js, cs, op))) == a : Bool}:
  match op:
    case Sv.OClaim{+due, +now, +fresh}:
      sg.aside_ce(a, runs, cs, Sv.claim(js, 0n, Sv.claim_jobs(cs), fresh, due, now))
    case Sv.ORecover{dead}:
      {==}
    case Sv.OFinish{+d, ran, failed, now}:
      sg.aside_fin(Sv.has_str(d, runs), me, runs, a, d, ran, failed, now, js, cs)
    case Sv.OCancel{n}:
      {==}
    case Sv.OResume{n, now}:
      {==}
    case Sv.OCreate{n, f}:
      {==}

def sg.aside_f(+runs: List<&2, String>, +me: Nat, +f: Sf.SfFile, +op: Sv.Op) -> {CronServe.sv_aside(CronServe.sv_reply(Sv.serve(runs, me, Sf.sf_disk(f), op))) == sg.torn(f) : Bool}:
  %Equal.sym(Sv.Served, Sv.serve(runs, me, Sf.sf_disk(f), op), Sv.go(runs, me, sg.torn(f), Sf.sf_pjs(Sf.sf_jobs(f)), Sf.sf_pcs(Sf.sf_claims_of(f)), op), sg.serve_go(runs, me, f, op)) : {CronServe.sv_aside(CronServe.sv_reply(_)) == sg.torn(f) : Bool}
  sg.aside_go(runs, me, sg.torn(f), Sf.sf_pjs(Sf.sf_jobs(f)), Sf.sf_pcs(Sf.sf_claims_of(f)), op)

# Bool and Nat
# ------------

def sg.or_t(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sg.or_fr(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LG.lg.tf({b == False{} : Bool}, h)
    case False{}:
      h

def sg.or_fl(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LG.lg.tf({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def sg.eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sg.eq_sym(p, q)

def sg.not_t(+b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LG.lg.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def sg.val(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def sg.some_inj(-A: Data, a: A, b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  %e : {a == sg.val(A, a, _) : A}
  {==}

def sg.isn(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def sg.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %Equal.sym(Maybe<&2, A>, None{}, Some{x}, e) : sg.isn(A, _, G)
  Unit{}
