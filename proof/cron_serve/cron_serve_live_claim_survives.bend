# eukhe: the proof of LAW cron_serve_live_claim_survives
# The claim is at some position k of the file's claim records (lc.idx).
# An update the claim stays through answers it kept at k
# (cron_serve_live_claim_kept), and a rendered answer keeps a claim
# answered kept at its position (lc.keep); a read file is never moved
# aside, and a file not written stays. Other writers keep every claim.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ../../laws/cron_serve/safety.bend as CronServeSafety
import ./base/safety.bend as LSf
import ./base/logic.bend as LG

# The claim's position
# --------------------

def lc.Pos(+cs: List<&2, CronServeSafety.SfC>, +d: String, +j: Nat, +o: Nat) -> Type:
  (&k: Nat -> {List.get(&2, Sv.CRec, CronServeSafety.sf_pcs(cs), k) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>})

def lc.shift(+c: CronServeSafety.SfC, +t: List<&2, CronServeSafety.SfC>, -d: String, -j: Nat, -o: Nat, p: lc.Pos(t, d, j, o)) -> lc.Pos(c <> t, d, j, o):
  (k, e) = p
  (1n+k, e)

def lc.eq3(+x: String, +y: Nat, +z: Nat, +d: String, +j: Nat, +o: Nat, +ex: {x == d : String}, +ey: {y == j : Nat}, +ez: {z == o : Nat}) -> {Some{Sv.CKnown{x, y, z}} == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}:
  %Equal.sym(String, x, d, ex) : {Some{Sv.CKnown{_, y, z}} == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}
  %Equal.sym(Nat, y, j, ey) : {Some{Sv.CKnown{d, _, z}} == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}
  %Equal.sym(Nat, z, o, ez) : {Some{Sv.CKnown{d, j, _}} == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}
  {==}

def lc.hd(+b: Bool, +x: String, +y: Nat, +z: Nat, +t: List<&2, CronServeSafety.SfC>, +d: String, +j: Nat, +o: Nat, +eb: {Bool.and(String.eq(x, d), Bool.and(Nat.is_eq(y, j), Nat.is_eq(z, o))) == b : Bool}, +on: {Bool.or(b, CronServeSafety.sf_has_claim(d, j, o, t)) == True{} : Bool}, ih: {CronServeSafety.sf_has_claim(d, j, o, t) == True{} : Bool} -> lc.Pos(t, d, j, o)) -> lc.Pos(CronServeSafety.SfCK{x, y, z} <> t, d, j, o):
  match b:
    case True{}:
      +e2 = LG.lg.and_r(String.eq(x, d), Bool.and(Nat.is_eq(y, j), Nat.is_eq(z, o)), eb)
      (0n, lc.eq3(x, y, z, d, j, o, LG.lg.str_sound(x, d, LG.lg.and_l(String.eq(x, d), Bool.and(Nat.is_eq(y, j), Nat.is_eq(z, o)), eb)), LG.lg.eq_true(y, j, LG.lg.and_l(Nat.is_eq(y, j), Nat.is_eq(z, o), e2)), LG.lg.eq_true(z, o, LG.lg.and_r(Nat.is_eq(y, j), Nat.is_eq(z, o), e2))))
    case False{}:
      lc.shift(CronServeSafety.SfCK{x, y, z}, t, d, j, o, ih(on))

def lc.idx(+cs: List<&2, CronServeSafety.SfC>, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, cs) == True{} : Bool}) -> lc.Pos(cs, d, j, o):
  match cs:
    case Nil{}:
      LG.lg.ft(lc.Pos(Nil{}, d, j, o), on)
    case c <> +t:
      match c:
        case CronServeSafety.SfCK{+x, +y, +z}:
          lc.hd(Bool.and(String.eq(x, d), Bool.and(Nat.is_eq(y, j), Nat.is_eq(z, o))), x, y, z, t, d, j, o, {==}, on, h => lc.idx(t, d, j, o, h))
        case CronServeSafety.SfCR{w}:
          lc.shift(CronServeSafety.SfCR{w}, t, d, j, o, lc.idx(t, d, j, o, on))

# A claim answered kept stays
# ---------------------------

def lc.hm(+d: String, +j: Nat, +o: Nat, +m: Maybe<&2, List<&2, CronServeSafety.SfC>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      CronServeSafety.sf_has_claim(d, j, o, x)

def lc.cs(+m: Maybe<&2, List<&2, CronServeSafety.SfC>>, +c: CronServeSafety.SfC, +d: String, +j: Nat, +o: Nat, +ih: {lc.hm(d, j, o, m) == True{} : Bool}) -> {lc.hm(d, j, o, CronServeSafety.sf_cons(CronServeSafety.SfC, c, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match c:
        case CronServeSafety.SfCK{x1, y1, z1}:
          %Equal.sym(Bool, CronServeSafety.sf_has_claim(d, j, o, x), True{}, ih) : {Bool.or(Bool.and(String.eq(x1, d), Bool.and(Nat.is_eq(y1, j), Nat.is_eq(z1, o))), _) == True{} : Bool}
          LSf.sg.or_t(Bool.and(String.eq(x1, d), Bool.and(Nat.is_eq(y1, j), Nat.is_eq(z1, o))))
        case CronServeSafety.SfCR{y}:
          ih

def lc.cd(+c: Sv.CRec) -> String:
  match c:
    case Sv.CKnown{d, j, o}:
      d
    case Sv.CRaw{}:
      ""

def lc.cj(+c: Sv.CRec) -> Nat:
  match c:
    case Sv.CKnown{d, j, o}:
      j
    case Sv.CRaw{}:
      0n

def lc.co(+c: Sv.CRec) -> Nat:
  match c:
    case Sv.CKnown{d, j, o}:
      o
    case Sv.CRaw{}:
      0n

def lc.isk(+c: Sv.CRec, G: Type) -> Type:
  match c:
    case Sv.CKnown{d, j, o}:
      Unit
    case Sv.CRaw{}:
      G

# the claim at position 0, answered kept, is in what is rendered
def lc.c0(+m: Maybe<&2, List<&2, CronServeSafety.SfC>>, +c: CronServeSafety.SfC, +d: String, +j: Nat, +o: Nat, +at: {CronServeSafety.sf_pc(c) == Sv.CKnown{d, j, o} : Sv.CRec}) -> {lc.hm(d, j, o, CronServeSafety.sf_cons(CronServeSafety.SfC, c, m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match c:
        case CronServeSafety.SfCK{+x1, +y1, +z1}:
          +at2 = at
          +at3 = at
          %Equal.sym(String, x1, d, Equal.cong(Sv.CRec, String, q => lc.cd(q), Sv.CKnown{x1, y1, z1}, Sv.CKnown{d, j, o}, at)) : {Bool.or(Bool.and(String.eq(_, d), Bool.and(Nat.is_eq(y1, j), Nat.is_eq(z1, o))), CronServeSafety.sf_has_claim(d, j, o, x)) == True{} : Bool}
          %Equal.sym(Nat, y1, j, Equal.cong(Sv.CRec, Nat, q => lc.cj(q), Sv.CKnown{x1, y1, z1}, Sv.CKnown{d, j, o}, at2)) : {Bool.or(Bool.and(String.eq(d, d), Bool.and(Nat.is_eq(_, j), Nat.is_eq(z1, o))), CronServeSafety.sf_has_claim(d, j, o, x)) == True{} : Bool}
          %Equal.sym(Nat, z1, o, Equal.cong(Sv.CRec, Nat, q => lc.co(q), Sv.CKnown{x1, y1, z1}, Sv.CKnown{d, j, o}, at3)) : {Bool.or(Bool.and(String.eq(d, d), Bool.and(Nat.is_eq(j, j), Nat.is_eq(_, o))), CronServeSafety.sf_has_claim(d, j, o, x)) == True{} : Bool}
          %Equal.sym(Bool, String.eq(d, d), True{}, LG.lg.str_refl(d)) : {Bool.or(Bool.and(_, Bool.and(Nat.is_eq(j, j), Nat.is_eq(o, o))), CronServeSafety.sf_has_claim(d, j, o, x)) == True{} : Bool}
          %Equal.sym(Bool, Nat.is_eq(j, j), True{}, LG.lg.eq_refl(j)) : {Bool.or(Bool.and(True{}, Bool.and(_, Nat.is_eq(o, o))), CronServeSafety.sf_has_claim(d, j, o, x)) == True{} : Bool}
          %Equal.sym(Bool, Nat.is_eq(o, o), True{}, LG.lg.eq_refl(o)) : {Bool.or(Bool.and(True{}, Bool.and(True{}, _)), CronServeSafety.sf_has_claim(d, j, o, x)) == True{} : Bool}
          {==}
        case CronServeSafety.SfCR{y}:
          %Equal.sym(Sv.CRec, Sv.CRaw{}, Sv.CKnown{d, j, o}, at) : lc.isk(_, {lc.hm(d, j, o, CronServeSafety.sf_cons(CronServeSafety.SfC, CronServeSafety.SfCR{y}, Some{x})) == True{} : Bool})
          Unit{}

def lc.KD(+o: Sv.COut, G: Type) -> Type:
  match o:
    case Sv.CKeep{}:
      Unit
    case Sv.CDrop{}:
      G
    case Sv.CNew{k, d}:
      G

def lc.nk(+o: Sv.COut, -G: Type, +e: {Some{o} == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}) -> lc.KD(o, G):
  %Equal.sym(Sv.COut, o, Sv.CKeep{}, LSf.sg.some_inj(Sv.COut, o, Sv.CKeep{}, e)) : lc.KD(_, G)
  Unit{}

def lc.nc(+isc: Bool, +m: Maybe<&2, Nat>, +d2: String, +me: Nat, +r: Maybe<&2, List<&2, CronServeSafety.SfC>>, +d: String, +j: Nat, +o: Nat, +ih: {lc.hm(d, j, o, r) == True{} : Bool}) -> {lc.hm(d, j, o, CronServeSafety.sf_new_claim(isc, m, d2, me, r)) == True{} : Bool}:
  match isc:
    case False{}:
      {==}
    case True{}:
      match m:
        case None{}:
          {==}
        case Some{i}:
          lc.cs(r, CronServeSafety.SfCK{d2, i, me}, d, j, o, ih)

# a rendered answer keeps the claim answered kept at its position
def lc.keep(+co: List<&2, Sv.COut>, +cs: List<&2, CronServeSafety.SfC>, +k: Nat, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool, +d: String, +j: Nat, +o: Nat, +at: {List.get(&2, Sv.CRec, CronServeSafety.sf_pcs(cs), k) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}, +kp: {List.get(&2, Sv.COut, co, k) == Some{Sv.CKeep{}} : Maybe<&2, Sv.COut>}) -> {lc.hm(d, j, o, CronServeSafety.sf_render_c(co, cs, pjs, me, isc)) == True{} : Bool}:
  match co:
    case Nil{}:
      LSf.sg.none_some(Sv.COut, Sv.CKeep{}, {lc.hm(d, j, o, CronServeSafety.sf_render_c(Nil{}, cs, pjs, me, isc)) == True{} : Bool}, kp)
    case o1 <> ot:
      match o1:
        case Sv.CKeep{}:
          match cs:
            case Nil{}:
              LSf.sg.none_some(Sv.CRec, Sv.CKnown{d, j, o}, {lc.hm(d, j, o, CronServeSafety.sf_render_c(Sv.CKeep{} <> ot, Nil{}, pjs, me, isc)) == True{} : Bool}, at)
            case +c <> t:
              match k:
                case 0n:
                  lc.c0(CronServeSafety.sf_render_c(ot, t, pjs, me, isc), c, d, j, o, LSf.sg.some_inj(Sv.CRec, CronServeSafety.sf_pc(c), Sv.CKnown{d, j, o}, at))
                case 1n+q:
                  lc.cs(CronServeSafety.sf_render_c(ot, t, pjs, me, isc), c, d, j, o, lc.keep(ot, t, q, pjs, me, isc, d, j, o, at, kp))
        case Sv.CDrop{}:
          match cs:
            case Nil{}:
              LSf.sg.none_some(Sv.CRec, Sv.CKnown{d, j, o}, {lc.hm(d, j, o, CronServeSafety.sf_render_c(Sv.CDrop{} <> ot, Nil{}, pjs, me, isc)) == True{} : Bool}, at)
            case c <> t:
              match k:
                case 0n:
                  lc.nk(Sv.CDrop{}, {lc.hm(d, j, o, CronServeSafety.sf_render_c(Sv.CDrop{} <> ot, c <> t, pjs, me, isc)) == True{} : Bool}, kp)
                case 1n+q:
                  lc.keep(ot, t, q, pjs, me, isc, d, j, o, at, kp)
        case Sv.CNew{+k2, +d2}:
          match cs:
            case Nil{}:
              LSf.sg.none_some(Sv.CRec, Sv.CKnown{d, j, o}, {lc.hm(d, j, o, CronServeSafety.sf_render_c(Sv.CNew{k2, d2} <> ot, Nil{}, pjs, me, isc)) == True{} : Bool}, at)
            case c <> t:
              match k:
                case 0n:
                  lc.nk(Sv.CNew{k2, d2}, {lc.hm(d, j, o, CronServeSafety.sf_render_c(Sv.CNew{k2, d2} <> ot, c <> t, pjs, me, isc)) == True{} : Bool}, kp)
                case 1n+q:
                  lc.nc(isc, CronServe.sv_job_at(pjs, k2), d2, me, CronServeSafety.sf_render_c(ot, t, pjs, me, isc), d, j, o, lc.keep(ot, t, q, pjs, me, isc, d, j, o, at, kp))

# The update
# ----------

def lc.wr(+w: Bool, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +mc: Maybe<&2, List<&2, CronServeSafety.SfC>>, +js: List<&2, CronServeSafety.SfJ>, +cs: List<&2, CronServeSafety.SfC>, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, cs) == True{} : Bool}, +hm: {lc.hm(d, j, o, mc) == True{} : Bool}) -> {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(CronServeSafety.sf_written(w, False{}, CronServeSafety.SfRead{js, cs}, mj, mc))) == True{} : Bool}:
  match w:
    case False{}:
      on
    case True{}:
      match mj:
        case None{}:
          on
        case Some{js2}:
          match mc:
            case None{}:
              on
            case Some{cs2}:
              hm

def lc.read2(+js: List<&2, CronServeSafety.SfJ>, +cs: List<&2, CronServeSafety.SfC>, +runs: List<&2, String>, +p: Nat, +op: Sv.Op, +w: Bool, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, cs) == True{} : Bool}, +spares: {CronServe.sv_stays(p, runs, op, d, o) == True{} : Bool}, +k: Nat, +at: {List.get(&2, Sv.CRec, CronServeSafety.sf_pcs(cs), k) == Some{Sv.CKnown{d, j, o}} : Maybe<&2, Sv.CRec>}) -> {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(CronServeSafety.sf_written(w, False{}, CronServeSafety.SfRead{js, cs}, mj, CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs)}, op))), cs, CronServeSafety.sf_pjs(js), p, CronServeSafety.sf_isc(op))))) == True{} : Bool}:
  lc.wr(w, mj, CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs)}, op))), cs, CronServeSafety.sf_pjs(js), p, CronServeSafety.sf_isc(op)), js, cs, d, j, o, on, lc.keep(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs)}, op))), cs, k, CronServeSafety.sf_pjs(js), p, CronServeSafety.sf_isc(op), d, j, o, at, CronServe.cron_serve_live_claim_kept(runs, p, CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs), op, k, d, j, o, at, spares)))

def lc.read(+js: List<&2, CronServeSafety.SfJ>, +cs: List<&2, CronServeSafety.SfC>, +runs: List<&2, String>, +p: Nat, +op: Sv.Op, +w: Bool, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, cs) == True{} : Bool}, +spares: {CronServe.sv_stays(p, runs, op, d, o) == True{} : Bool}, pos: lc.Pos(cs, d, j, o)) -> {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(CronServeSafety.sf_written(w, False{}, CronServeSafety.SfRead{js, cs}, mj, CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Parsed{CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs)}, op))), cs, CronServeSafety.sf_pjs(js), p, CronServeSafety.sf_isc(op))))) == True{} : Bool}:
  (k, at) = pos
  lc.read2(js, cs, runs, p, op, w, mj, d, j, o, on, spares, k, at)

def lc.up(+f: CronServeSafety.SfFile, +runs: List<&2, String>, +p: Nat, +op: Sv.Op, +w: Bool, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +d: String, +j: Nat, +o: Nat, +dead: List<&2, Nat>, +aside: List<&2, Nat>, +on: {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(f)) == True{} : Bool}, +spares: {CronServe.sv_stays(p, runs, op, d, o) == True{} : Bool}) -> {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(w, LSf.sg.torn(f), f, mj, CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, CronServeSafety.sf_disk(f), op))), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op))), dead, CronServeSafety.sf_moved(LSf.sg.torn(f), f, aside)})) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      LG.lg.ft({CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(w, False{}, CronServeSafety.SfMissing{}, mj, CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Missing{}, op))), Nil{}, Nil{}, p, CronServeSafety.sf_isc(op))), dead, aside})) == True{} : Bool}, on)
    case CronServeSafety.SfTorn{t}:
      LG.lg.ft({CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(w, True{}, CronServeSafety.SfTorn{t}, mj, CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.serve(runs, p, Sv.Torn{}, op))), Nil{}, Nil{}, p, CronServeSafety.sf_isc(op))), dead, t <> aside})) == True{} : Bool}, on)
    case CronServeSafety.SfRead{+js, +cs}:
      +on2 = on
      lc.read(js, cs, runs, p, op, w, mj, d, j, o, on, spares, lc.idx(cs, d, j, o, on2))

# Other events
# ------------

def lc.app.k(+a: Bool, +b: Bool, +c: Bool, +on: {Bool.or(a, b) == True{} : Bool}, ih: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ih(on)

def lc.app(+cs: List<&2, CronServeSafety.SfC>, +x: Nat, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, cs) == True{} : Bool}) -> {CronServeSafety.sf_has_claim(d, j, o, List.append(&2, CronServeSafety.SfC, cs, [CronServeSafety.SfCR{x}])) == True{} : Bool}:
  match cs:
    case Nil{}:
      on
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x1, y1, z1}:
          lc.app.k(Bool.and(String.eq(x1, d), Bool.and(Nat.is_eq(y1, j), Nat.is_eq(z1, o))), CronServeSafety.sf_has_claim(d, j, o, t), CronServeSafety.sf_has_claim(d, j, o, List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCR{x}])), on, e => lc.app(t, x, d, j, o, e))
        case CronServeSafety.SfCR{y}:
          lc.app(t, x, d, j, o, on)

def lc.rc(+f: CronServeSafety.SfFile, +x: Nat, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(f)) == True{} : Bool}) -> {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(CronServeSafety.sf_add_claim(x, f))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      on
    case CronServeSafety.SfTorn{t}:
      on
    case CronServeSafety.SfRead{js, cs}:
      lc.app(cs, x, d, j, o, on)

def lc.rj(+f: CronServeSafety.SfFile, +x: Nat, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(f)) == True{} : Bool}) -> {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(CronServeSafety.sf_add_job(x, f))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      on
    case CronServeSafety.SfTorn{t}:
      on
    case CronServeSafety.SfRead{js, cs}:
      on

def lc.fa(+f: CronServeSafety.SfFile, +k: Nat, +g: CS.Fact, +d: String, +j: Nat, +o: Nat, +on: {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(f)) == True{} : Bool}) -> {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims_of(CronServeSafety.sf_facts(k, g, f))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      on
    case CronServeSafety.SfTorn{t}:
      on
    case CronServeSafety.SfRead{js, cs}:
      on

def CronServeSafety.cron_serve_live_claim_survives(w, e, d, j, o, on, spares):
  match w:
    case CronServeSafety.SfWorld{+f, +dead, +aside}:
      match e:
        case CronServeSafety.SfUp{+p, +runs, +op}:
          +op2 = CronServeSafety.sf_op(op, dead)
          +r = CronServe.sv_reply(Sv.serve(runs, p, CronServeSafety.sf_disk(f), op2))
          +mj = CronServeSafety.sf_render_j(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2))
          +mc = CronServeSafety.sf_render_c(CronServe.sv_claims_out(r), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2))
          %Equal.sym(CronServeSafety.SfWorld, CronServeSafety.sf_apply(r, f, op2, p, dead, aside), CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), CronServe.sv_aside(r), f, mj, mc), dead, CronServeSafety.sf_moved(CronServe.sv_aside(r), f, aside)}, LSf.sg.up(r, f, op2, p, dead, aside)) : {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims(_)) == True{} : Bool}
          %Equal.sym(Bool, CronServe.sv_aside(r), LSf.sg.torn(f), LSf.sg.aside_f(runs, p, f, op2)) : {CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), _, f, mj, mc), dead, CronServeSafety.sf_moved(_, f, aside)})) == True{} : Bool}
          lc.up(f, runs, p, op2, CronServe.sv_write(r), mj, d, j, o, dead, aside, on, spares)
        case CronServeSafety.SfDie{q}:
          on
        case CronServeSafety.SfRawJob{+x}:
          lc.rj(f, x, d, j, o, on)
        case CronServeSafety.SfRawClaim{+x}:
          lc.rc(f, x, d, j, o, on)
        case CronServeSafety.SfFacts{+k, +g}:
          lc.fa(f, k, g, d, j, o, on)
        case CronServeSafety.SfCorrupt{x}:
          LG.lg.ft({CronServeSafety.sf_has_claim(d, j, o, CronServeSafety.sf_claims(CronServeSafety.sf_step(CronServeSafety.SfWorld{f, dead, aside}, CronServeSafety.SfCorrupt{x}))) == True{} : Bool}, spares)
