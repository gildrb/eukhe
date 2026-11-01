# eukhe: the proof of LAW cron_serve_one_claim_per_job
# By induction over the events: every event keeps "no two known claims of
# one job". An update renders, per op: a claim pass keeps every claim
# record and adds new claims, each of a known job with no claim on record
# and none made before it in the pass (cron_serve_claims_unclaimed's
# lemma PCU.cu.pass); a recovery keeps the claims the verdicts keep
# (PDC.dc2.f1); a finish keeps every claim or drops the first of its
# dispatch; a cancel, a resume and a create keep every claim. Dropping
# claims keeps the property; a file not written stays, a file moved aside
# has no claims. Other writers add a claim this build cannot read, or
# touch no claim; a corrupt file has none.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../laws/cron_serve/serve.bend as CronServe
import ../../laws/cron_serve/safety.bend as CronServeSafety
import ./base/safety.bend as LSf
import ./base/logic.bend as LG
import ./base/exact.bend as LSx
import ./cron_serve_claims_unclaimed.bend as PCU
import ./cron_serve_dead_claims_cleared.bend as PDC

# Terms
# -----

def oe.m(+m: Maybe<&2, List<&2, CronServeSafety.SfC>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      CronServeSafety.sf_one_each(x)

def oe.app(+xs: List<&2, CronServeSafety.SfC>, +m: Maybe<&2, List<&2, CronServeSafety.SfC>>) -> Maybe<&2, List<&2, CronServeSafety.SfC>>:
  match m:
    case None{}:
      None{}
    case Some{ys}:
      Some{List.append(&2, CronServeSafety.SfC, xs, ys)}

# every x of xs is in ys
def oe.allin(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(CronServe.sv_has(x, ys), oe.allin(t, ys))

def oe.addm(+xs: List<&2, CronServeSafety.SfC>, +m: Maybe<&2, Nat>, +d: String, +me: Nat) -> List<&2, CronServeSafety.SfC>:
  match m:
    case None{}:
      xs
    case Some{i}:
      List.append(&2, CronServeSafety.SfC, xs, [CronServeSafety.SfCK{d, i, me}])

# the claims without the first known claim of dispatch d
def oe.rmf.pick(+b: Bool, +c: CronServeSafety.SfC, +t: List<&2, CronServeSafety.SfC>, +r: List<&2, CronServeSafety.SfC>) -> List<&2, CronServeSafety.SfC>:
  match b:
    case True{}:
      t
    case False{}:
      c <> r

def oe.rmf(+d: String, +cs: List<&2, CronServeSafety.SfC>) -> List<&2, CronServeSafety.SfC>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> +t:
      match c:
        case CronServeSafety.SfCK{x, j, o}:
          oe.rmf.pick(String.eq(x, d), CronServeSafety.SfCK{x, j, o}, t, oe.rmf(d, t))
        case CronServeSafety.SfCR{y}:
          CronServeSafety.SfCR{y} <> oe.rmf(d, t)

# Lists
# -----

def oe.app_nil(+xs: List<&2, CronServeSafety.SfC>) -> {List.append(&2, CronServeSafety.SfC, xs, Nil{}) == xs : List<&2, CronServeSafety.SfC>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(List<&2, CronServeSafety.SfC>, List<&2, CronServeSafety.SfC>, z => x <> z, List.append(&2, CronServeSafety.SfC, t, Nil{}), t, oe.app_nil(t))

def oe.app_snoc(+xs: List<&2, CronServeSafety.SfC>, +c: CronServeSafety.SfC, +n: List<&2, CronServeSafety.SfC>) -> {List.append(&2, CronServeSafety.SfC, List.append(&2, CronServeSafety.SfC, xs, [c]), n) == List.append(&2, CronServeSafety.SfC, xs, c <> n) : List<&2, CronServeSafety.SfC>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(List<&2, CronServeSafety.SfC>, List<&2, CronServeSafety.SfC>, z => x <> z, List.append(&2, CronServeSafety.SfC, List.append(&2, CronServeSafety.SfC, t, [c]), n), List.append(&2, CronServeSafety.SfC, t, c <> n), oe.app_snoc(t, c, n))

def oe.taken_snoc(+xs: List<&2, CronServeSafety.SfC>, +d: String, +i: Nat, +me: Nat) -> {CronServe.sv_taken(CronServeSafety.sf_pcs(List.append(&2, CronServeSafety.SfC, xs, [CronServeSafety.SfCK{d, i, me}]))) == List.append(&2, Nat, CronServe.sv_taken(CronServeSafety.sf_pcs(xs)), [i]) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, j, o}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => j <> z, CronServe.sv_taken(CronServeSafety.sf_pcs(List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCK{d, i, me}]))), List.append(&2, Nat, CronServe.sv_taken(CronServeSafety.sf_pcs(t)), [i]), oe.taken_snoc(t, d, i, me))
        case CronServeSafety.SfCR{y}:
          oe.taken_snoc(t, d, i, me)

# Membership
# ----------

def oe.weak(+xs: List<&2, Nat>, +i: Nat, +ys: List<&2, Nat>, +h: {oe.allin(xs, ys) == True{} : Bool}) -> {oe.allin(xs, i <> ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      +hx = LG.lg.and_l(CronServe.sv_has(x, ys), oe.allin(t, ys), h)
      %Equal.sym(Bool, CronServe.sv_has(x, ys), True{}, hx) : {Bool.and(Bool.or(Nat.is_eq(i, x), _), oe.allin(t, i <> ys)) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Nat.is_eq(i, x), True{}), True{}, LSf.sg.or_t(Nat.is_eq(i, x))) : {Bool.and(_, oe.allin(t, i <> ys)) == True{} : Bool}
      oe.weak(t, i, ys, LG.lg.and_r(CronServe.sv_has(x, ys), oe.allin(t, ys), h))

def oe.refl(+xs: List<&2, Nat>) -> {oe.allin(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, LG.lg.eq_refl(x)) : {Bool.and(Bool.or(_, CronServe.sv_has(x, t)), oe.allin(t, x <> t)) == True{} : Bool}
      oe.weak(t, x, t, oe.refl(t))

def oe.allin_snoc(+xs: List<&2, Nat>, +i: Nat, +ys: List<&2, Nat>, +h: {oe.allin(xs, ys) == True{} : Bool}) -> {oe.allin(List.append(&2, Nat, xs, [i]), i <> ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(i, i), True{}, LG.lg.eq_refl(i)) : {Bool.and(Bool.or(_, CronServe.sv_has(i, ys)), True{}) == True{} : Bool}
      {==}
    case x <> t:
      +hx = LG.lg.and_l(CronServe.sv_has(x, ys), oe.allin(t, ys), h)
      %Equal.sym(Bool, CronServe.sv_has(x, ys), True{}, hx) : {Bool.and(Bool.or(Nat.is_eq(i, x), _), oe.allin(List.append(&2, Nat, t, [i]), i <> ys)) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Nat.is_eq(i, x), True{}), True{}, LSf.sg.or_t(Nat.is_eq(i, x))) : {Bool.and(_, oe.allin(List.append(&2, Nat, t, [i]), i <> ys)) == True{} : Bool}
      oe.allin_snoc(t, i, ys, LG.lg.and_r(CronServe.sv_has(x, ys), oe.allin(t, ys), h))

def oe.ne(+b: Bool, +j: Nat, +i: Nat, +ys: List<&2, Nat>, +eb: {Nat.is_eq(j, i) == b : Bool}, +hj: {CronServe.sv_has(j, ys) == True{} : Bool}, +hi: {CronServe.sv_has(i, ys) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LG.lg.tf({True{} == False{} : Bool}, Equal.trans(Bool, True{}, CronServe.sv_has(i, ys), False{}, Equal.trans(Bool, True{}, CronServe.sv_has(j, ys), CronServe.sv_has(i, ys), Equal.sym(Bool, CronServe.sv_has(j, ys), True{}, hj), Equal.cong(Nat, Bool, n => CronServe.sv_has(n, ys), j, i, LG.lg.eq_true(j, i, eb))), hi))
    case False{}:
      {==}

# a job not in ys has no claim in a list whose claims' jobs are all in ys
def oe.notin(+xs: List<&2, CronServeSafety.SfC>, +i: Nat, +ys: List<&2, Nat>, +ha: {oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(xs)), ys) == True{} : Bool}, +hi: {CronServe.sv_has(i, ys) == False{} : Bool}) -> {CronServeSafety.sf_has_job(i, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, j, o}:
          %Equal.sym(Bool, Nat.is_eq(j, i), False{}, oe.ne(Nat.is_eq(j, i), j, i, ys, {==}, LG.lg.and_l(CronServe.sv_has(j, ys), oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(t)), ys), ha), hi)) : {Bool.or(_, CronServeSafety.sf_has_job(i, t)) == False{} : Bool}
          oe.notin(t, i, ys, LG.lg.and_r(CronServe.sv_has(j, ys), oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(t)), ys), ha), hi)
        case CronServeSafety.SfCR{y}:
          oe.notin(t, i, ys, ha, hi)

def oe.or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, b) == False{} : Bool}
  hb

def oe.has_snoc(+t: List<&2, CronServeSafety.SfC>, +j: Nat, +c: CronServeSafety.SfC, +i: Nat, +hc: {CronServeSafety.sf_has_job(j, [c]) == False{} : Bool}, +ht: {CronServeSafety.sf_has_job(j, t) == False{} : Bool}) -> {CronServeSafety.sf_has_job(j, List.append(&2, CronServeSafety.SfC, t, [c])) == False{} : Bool}:
  match t:
    case Nil{}:
      hc
    case a <> u:
      match a:
        case CronServeSafety.SfCK{x, y, o}:
          oe.or_ff(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, List.append(&2, CronServeSafety.SfC, u, [c])), LSf.sg.or_fl(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, u), ht), oe.has_snoc(u, j, c, i, hc, LSf.sg.or_fr(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, u), ht)))
        case CronServeSafety.SfCR{z}:
          oe.has_snoc(u, j, c, i, hc, ht)

# a claim of a job with no claim in xs, added last, keeps one claim per job
def oe.snoc(+xs: List<&2, CronServeSafety.SfC>, +d: String, +i: Nat, +me: Nat, +h: {CronServeSafety.sf_one_each(xs) == True{} : Bool}, +hn: {CronServeSafety.sf_has_job(i, xs) == False{} : Bool}) -> {CronServeSafety.sf_one_each(List.append(&2, CronServeSafety.SfC, xs, [CronServeSafety.SfCK{d, i, me}])) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, j, o}:
          +hji = LSf.sg.or_fl(Nat.is_eq(j, i), CronServeSafety.sf_has_job(i, t), hn)
          +hij = Equal.trans(Bool, Nat.is_eq(i, j), Nat.is_eq(j, i), False{}, LSf.sg.eq_sym(i, j), hji)
          +hc = oe.or_ff(Nat.is_eq(i, j), False{}, hij, {==})
          +ht = LSf.sg.not_t(CronServeSafety.sf_has_job(j, t), LG.lg.and_l(Bool.not(CronServeSafety.sf_has_job(j, t)), CronServeSafety.sf_one_each(t), h))
          %Equal.sym(Bool, CronServeSafety.sf_has_job(j, List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCK{d, i, me}])), False{}, oe.has_snoc(t, j, CronServeSafety.SfCK{d, i, me}, i, hc, ht)) : {Bool.and(Bool.not(_), CronServeSafety.sf_one_each(List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCK{d, i, me}]))) == True{} : Bool}
          oe.snoc(t, d, i, me, LG.lg.and_r(Bool.not(CronServeSafety.sf_has_job(j, t)), CronServeSafety.sf_one_each(t), h), LSf.sg.or_fr(Nat.is_eq(j, i), CronServeSafety.sf_has_job(i, t), hn))
        case CronServeSafety.SfCR{y}:
          oe.snoc(t, d, i, me, h, hn)

# Sublists keep one claim per job
# -------------------------------

def oe.drop_has(+b: Bool, +c: CronServeSafety.SfC, +t: List<&2, CronServeSafety.SfC>, +r: List<&2, CronServeSafety.SfC>, +j: Nat, +hc: {CronServeSafety.sf_has_job(j, [c]) == False{} : Bool}, +hr: {CronServeSafety.sf_has_job(j, r) == False{} : Bool}, +ht: {CronServeSafety.sf_has_job(j, t) == False{} : Bool}) -> {CronServeSafety.sf_has_job(j, oe.rmf.pick(b, c, t, r)) == False{} : Bool}:
  match b:
    case True{}:
      ht
    case False{}:
      match c:
        case CronServeSafety.SfCK{x, y, o}:
          oe.or_ff(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, r), LSf.sg.or_fl(Nat.is_eq(y, j), False{}, hc), hr)
        case CronServeSafety.SfCR{z}:
          hr

def oe.rmf_has(+d: String, +cs: List<&2, CronServeSafety.SfC>, +j: Nat, +h: {CronServeSafety.sf_has_job(j, cs) == False{} : Bool}) -> {CronServeSafety.sf_has_job(j, oe.rmf(d, cs)) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, y, o}:
          +ht = LSf.sg.or_fr(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, t), h)
          oe.drop_has(String.eq(x, d), CronServeSafety.SfCK{x, y, o}, t, oe.rmf(d, t), j, oe.or_ff(Nat.is_eq(y, j), False{}, LSf.sg.or_fl(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, t), h), {==}), oe.rmf_has(d, t, j, ht), ht)
        case CronServeSafety.SfCR{z}:
          oe.rmf_has(d, t, j, h)

def oe.rmf_pick(+b: Bool, +x: String, +y: Nat, +o: Nat, +t: List<&2, CronServeSafety.SfC>, +r: List<&2, CronServeSafety.SfC>, +ht: {CronServeSafety.sf_one_each(t) == True{} : Bool}, +hr: {CronServeSafety.sf_one_each(r) == True{} : Bool}, +hy: {CronServeSafety.sf_has_job(y, r) == False{} : Bool}) -> {CronServeSafety.sf_one_each(oe.rmf.pick(b, CronServeSafety.SfCK{x, y, o}, t, r)) == True{} : Bool}:
  match b:
    case True{}:
      ht
    case False{}:
      %Equal.sym(Bool, CronServeSafety.sf_has_job(y, r), False{}, hy) : {Bool.and(Bool.not(_), CronServeSafety.sf_one_each(r)) == True{} : Bool}
      hr

def oe.rmf_oe(+d: String, +cs: List<&2, CronServeSafety.SfC>, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {CronServeSafety.sf_one_each(oe.rmf(d, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, y, o}:
          +ht = LG.lg.and_r(Bool.not(CronServeSafety.sf_has_job(y, t)), CronServeSafety.sf_one_each(t), h)
          +hy = LSf.sg.not_t(CronServeSafety.sf_has_job(y, t), LG.lg.and_l(Bool.not(CronServeSafety.sf_has_job(y, t)), CronServeSafety.sf_one_each(t), h))
          oe.rmf_pick(String.eq(x, d), x, y, o, t, oe.rmf(d, t), ht, oe.rmf_oe(d, t, ht), oe.rmf_has(d, t, y, hy))
        case CronServeSafety.SfCR{z}:
          oe.rmf_oe(d, t, h)

def oe.fp_has(+b: Bool, +c: CronServeSafety.SfC, +r: List<&2, CronServeSafety.SfC>, +j: Nat, +hc: {CronServeSafety.sf_has_job(j, [c]) == False{} : Bool}, +hr: {CronServeSafety.sf_has_job(j, r) == False{} : Bool}) -> {CronServeSafety.sf_has_job(j, PDC.dc2.fpick(b, c, r)) == False{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      match c:
        case CronServeSafety.SfCK{x, y, o}:
          oe.or_ff(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, r), LSf.sg.or_fl(Nat.is_eq(y, j), False{}, hc), hr)
        case CronServeSafety.SfCR{z}:
          hr

def oe.fp_oe(+b: Bool, +x: String, +y: Nat, +o: Nat, +r: List<&2, CronServeSafety.SfC>, +hr: {CronServeSafety.sf_one_each(r) == True{} : Bool}, +hy: {CronServeSafety.sf_has_job(y, r) == False{} : Bool}) -> {CronServeSafety.sf_one_each(PDC.dc2.fpick(b, CronServeSafety.SfCK{x, y, o}, r)) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      %Equal.sym(Bool, CronServeSafety.sf_has_job(y, r), False{}, hy) : {Bool.and(Bool.not(_), CronServeSafety.sf_one_each(r)) == True{} : Bool}
      hr

def oe.filt_has(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +cs: List<&2, CronServeSafety.SfC>, +j: Nat, +h: {CronServeSafety.sf_has_job(j, cs) == False{} : Bool}) -> {CronServeSafety.sf_has_job(j, PDC.dc2.filt(me, runs, dead, cs)) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, y, o}:
          +ht = LSf.sg.or_fr(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, t), h)
          oe.fp_has(Sv.clears(me, runs, dead, Sv.CKnown{x, y, o}), CronServeSafety.SfCK{x, y, o}, PDC.dc2.filt(me, runs, dead, t), j, oe.or_ff(Nat.is_eq(y, j), False{}, LSf.sg.or_fl(Nat.is_eq(y, j), CronServeSafety.sf_has_job(j, t), h), {==}), oe.filt_has(me, runs, dead, t, j, ht))
        case CronServeSafety.SfCR{z}:
          oe.filt_has(me, runs, dead, t, j, h)

def oe.filt_oe(+me: Nat, +runs: List<&2, String>, +dead: List<&2, Nat>, +cs: List<&2, CronServeSafety.SfC>, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {CronServeSafety.sf_one_each(PDC.dc2.filt(me, runs, dead, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, y, o}:
          +ht = LG.lg.and_r(Bool.not(CronServeSafety.sf_has_job(y, t)), CronServeSafety.sf_one_each(t), h)
          +hy = LSf.sg.not_t(CronServeSafety.sf_has_job(y, t), LG.lg.and_l(Bool.not(CronServeSafety.sf_has_job(y, t)), CronServeSafety.sf_one_each(t), h))
          oe.fp_oe(Sv.clears(me, runs, dead, Sv.CKnown{x, y, o}), x, y, o, PDC.dc2.filt(me, runs, dead, t), oe.filt_oe(me, runs, dead, t, ht), oe.filt_has(me, runs, dead, t, y, hy))
        case CronServeSafety.SfCR{z}:
          oe.filt_oe(me, runs, dead, t, h)

# Rendering
# ---------

def oe.k0(+cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool) -> {CronServeSafety.sf_render_c(Sv.keep(CronServeSafety.sf_pcs(cs)), cs, pjs, me, isc) == Some{cs} : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(Sv.keep(CronServeSafety.sf_pcs(t)), t, pjs, me, isc), Some{t}, oe.k0(t, pjs, me, isc)) : {CronServeSafety.sf_cons(CronServeSafety.SfC, c, _) == Some{c <> t} : Maybe<&2, List<&2, CronServeSafety.SfC>>}
      {==}

def oe.app_nil_l(+m: Maybe<&2, List<&2, CronServeSafety.SfC>>) -> {oe.app(Nil{}, m) == m : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match m:
    case None{}:
      {==}
    case Some{ys}:
      {==}

def oe.k1c(+m: Maybe<&2, List<&2, CronServeSafety.SfC>>, +c: CronServeSafety.SfC, +t: List<&2, CronServeSafety.SfC>) -> {CronServeSafety.sf_cons(CronServeSafety.SfC, c, oe.app(t, m)) == oe.app(c <> t, m) : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match m:
    case None{}:
      {==}
    case Some{ys}:
      {==}

def oe.k1(+cs: List<&2, CronServeSafety.SfC>, +cn: List<&2, Sv.COut>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool) -> {CronServeSafety.sf_render_c(List.append(&2, Sv.COut, Sv.keep(CronServeSafety.sf_pcs(cs)), cn), cs, pjs, me, isc) == oe.app(cs, CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc)) : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match cs:
    case Nil{}:
      Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, oe.app(Nil{}, CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc)), CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc), oe.app_nil_l(CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc)))
    case c <> t:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(List.append(&2, Sv.COut, Sv.keep(CronServeSafety.sf_pcs(t)), cn), t, pjs, me, isc), oe.app(t, CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc)), oe.k1(t, cn, pjs, me, isc)) : {CronServeSafety.sf_cons(CronServeSafety.SfC, c, _) == oe.app(c <> t, CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc)) : Maybe<&2, List<&2, CronServeSafety.SfC>>}
      oe.k1c(CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc), c, t)

def oe.dfb(+b: Bool, +x: String, +j: Nat, +o: Nat, +t: List<&2, CronServeSafety.SfC>, +d: String, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool, +ih: {CronServeSafety.sf_render_c(Sv.drop_first(d, CronServeSafety.sf_pcs(t)), t, pjs, me, isc) == Some{oe.rmf(d, t)} : Maybe<&2, List<&2, CronServeSafety.SfC>>}) -> {CronServeSafety.sf_render_c(Sv.drop_first.pick(b, CronServeSafety.sf_pcs(t), Sv.drop_first(d, CronServeSafety.sf_pcs(t))), CronServeSafety.SfCK{x, j, o} <> t, pjs, me, isc) == Some{oe.rmf.pick(b, CronServeSafety.SfCK{x, j, o}, t, oe.rmf(d, t))} : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match b:
    case True{}:
      oe.k0(t, pjs, me, isc)
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(Sv.drop_first(d, CronServeSafety.sf_pcs(t)), t, pjs, me, isc), Some{oe.rmf(d, t)}, ih) : {CronServeSafety.sf_cons(CronServeSafety.SfC, CronServeSafety.SfCK{x, j, o}, _) == Some{CronServeSafety.SfCK{x, j, o} <> oe.rmf(d, t)} : Maybe<&2, List<&2, CronServeSafety.SfC>>}
      {==}

def oe.df(+d: String, +cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool) -> {CronServeSafety.sf_render_c(Sv.drop_first(d, CronServeSafety.sf_pcs(cs)), cs, pjs, me, isc) == Some{oe.rmf(d, cs)} : Maybe<&2, List<&2, CronServeSafety.SfC>>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{x, j, o}:
          oe.dfb(String.eq(x, d), x, j, o, t, d, pjs, me, isc, oe.df(d, t, pjs, me, isc))
        case CronServeSafety.SfCR{y}:
          %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(Sv.drop_first(d, CronServeSafety.sf_pcs(t)), t, pjs, me, isc), Some{oe.rmf(d, t)}, oe.df(d, t, pjs, me, isc)) : {CronServeSafety.sf_cons(CronServeSafety.SfC, CronServeSafety.SfCR{y}, _) == Some{CronServeSafety.SfCR{y} <> oe.rmf(d, t)} : Maybe<&2, List<&2, CronServeSafety.SfC>>}
          {==}

# The new claims of a claim pass
# ------------------------------

def oe.h1(+m: Maybe<&2, Nat>, +xs: List<&2, CronServeSafety.SfC>, +d: String, +me: Nat, +ys: List<&2, Nat>, +h1: {CronServeSafety.sf_one_each(xs) == True{} : Bool}, +h2: {oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(xs)), ys) == True{} : Bool}, +ok: {CronServe.sv_new.ok(m, ys) == True{} : Bool}) -> {CronServeSafety.sf_one_each(oe.addm(xs, m, d, me)) == True{} : Bool}:
  match m:
    case None{}:
      h1
    case Some{i}:
      oe.snoc(xs, d, i, me, h1, oe.notin(xs, i, ys, h2, LSf.sg.not_t(CronServe.sv_has(i, ys), ok)))

def oe.h2(+m: Maybe<&2, Nat>, +xs: List<&2, CronServeSafety.SfC>, +d: String, +me: Nat, +ys: List<&2, Nat>, +h2: {oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(xs)), ys) == True{} : Bool}) -> {oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(oe.addm(xs, m, d, me))), CronServe.sv_new.add(m, ys)) == True{} : Bool}:
  match m:
    case None{}:
      h2
    case Some{i}:
      %Equal.sym(List<&2, Nat>, CronServe.sv_taken(CronServeSafety.sf_pcs(List.append(&2, CronServeSafety.SfC, xs, [CronServeSafety.SfCK{d, i, me}]))), List.append(&2, Nat, CronServe.sv_taken(CronServeSafety.sf_pcs(xs)), [i]), oe.taken_snoc(xs, d, i, me)) : {oe.allin(_, i <> ys) == True{} : Bool}
      oe.allin_snoc(CronServe.sv_taken(CronServeSafety.sf_pcs(xs)), i, ys, h2)

def oe.u_r(+r: Maybe<&2, List<&2, CronServeSafety.SfC>>, +xs: List<&2, CronServeSafety.SfC>, +c: CronServeSafety.SfC, +ih: {oe.m(oe.app(List.append(&2, CronServeSafety.SfC, xs, [c]), r)) == True{} : Bool}) -> {oe.m(oe.app(xs, CronServeSafety.sf_cons(CronServeSafety.SfC, c, r))) == True{} : Bool}:
  match r:
    case None{}:
      {==}
    case Some{n}:
      %oe.app_snoc(xs, c, n) : {CronServeSafety.sf_one_each(_) == True{} : Bool}
      ih

def oe.u_new(+isc: Bool, +m: Maybe<&2, Nat>, +xs: List<&2, CronServeSafety.SfC>, +d: String, +me: Nat, +r: Maybe<&2, List<&2, CronServeSafety.SfC>>, +ih: {oe.m(oe.app(oe.addm(xs, m, d, me), r)) == True{} : Bool}) -> {oe.m(oe.app(xs, CronServeSafety.sf_new_claim(isc, m, d, me, r))) == True{} : Bool}:
  match isc:
    case False{}:
      {==}
    case True{}:
      match m:
        case None{}:
          {==}
        case Some{i}:
          oe.u_r(r, xs, CronServeSafety.SfCK{d, i, me}, ih)

# the new claims a claim pass answers, added after claims xs whose jobs
# are all in ys, keep one claim per job
def oe.u(+cn: List<&2, Sv.COut>, +xs: List<&2, CronServeSafety.SfC>, +ys: List<&2, Nat>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool, +h1: {CronServeSafety.sf_one_each(xs) == True{} : Bool}, +h2: {oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(xs)), ys) == True{} : Bool}, +h3: {CronServe.sv_new_unclaimed(cn, pjs, ys) == True{} : Bool}) -> {oe.m(oe.app(xs, CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, isc))) == True{} : Bool}:
  match cn:
    case Nil{}:
      %Equal.sym(List<&2, CronServeSafety.SfC>, List.append(&2, CronServeSafety.SfC, xs, Nil{}), xs, oe.app_nil(xs)) : {CronServeSafety.sf_one_each(_) == True{} : Bool}
      h1
    case o <> ot:
      match o:
        case Sv.CKeep{}:
          {==}
        case Sv.CDrop{}:
          {==}
        case Sv.CNew{k, d}:
          +m = CronServe.sv_job_at(pjs, k)
          oe.u_new(isc, m, xs, d, me, CronServeSafety.sf_render_c(ot, Nil{}, pjs, me, isc), oe.u(ot, oe.addm(xs, m, d, me), CronServe.sv_new.add(m, ys), pjs, me, isc, oe.h1(m, xs, d, me, ys, h1, h2, LG.lg.and_l(CronServe.sv_new.ok(m, ys), CronServe.sv_new_unclaimed(ot, pjs, CronServe.sv_new.add(m, ys)), h3)), oe.h2(m, xs, d, me, ys, h2), LG.lg.and_r(CronServe.sv_new.ok(m, ys), CronServe.sv_new_unclaimed(ot, pjs, CronServe.sv_new.add(m, ys)), h3)))

# The update, per op
# ------------------

def oe.claim(+p: Sv.Pass, +a: Bool, +runs: List<&2, String>, +cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}, +hn: {CronServe.sv_new_unclaimed(PCU.cu.news(p), pjs, Sv.claim_jobs(CronServeSafety.sf_pcs(cs))) == True{} : Bool}) -> {oe.m(CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.claim.end(a, runs, CronServeSafety.sf_pcs(cs), p))), cs, pjs, me, True{})) == True{} : Bool}:
  match p:
    case Sv.Pass{jo, cn, ds}:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(List.append(&2, Sv.COut, Sv.keep(CronServeSafety.sf_pcs(cs)), cn), cs, pjs, me, True{}), oe.app(cs, CronServeSafety.sf_render_c(cn, Nil{}, pjs, me, True{})), oe.k1(cs, cn, pjs, me, True{})) : {oe.m(_) == True{} : Bool}
      +h2 = Equal.trans(Bool, oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(cs)), Sv.claim_jobs(CronServeSafety.sf_pcs(cs))), oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(cs)), CronServe.sv_taken(CronServeSafety.sf_pcs(cs))), True{}, Equal.cong(List<&2, Nat>, Bool, z => oe.allin(CronServe.sv_taken(CronServeSafety.sf_pcs(cs)), z), Sv.claim_jobs(CronServeSafety.sf_pcs(cs)), CronServe.sv_taken(CronServeSafety.sf_pcs(cs)), LSx.sx.taken(CronServeSafety.sf_pcs(cs))), oe.refl(CronServe.sv_taken(CronServeSafety.sf_pcs(cs))))
      oe.u(cn, cs, Sv.claim_jobs(CronServeSafety.sf_pcs(cs)), pjs, me, True{}, h, h2, hn)

def oe.keep(+cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +isc: Bool, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {oe.m(CronServeSafety.sf_render_c(Sv.keep(CronServeSafety.sf_pcs(cs)), cs, pjs, me, isc)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(Sv.keep(CronServeSafety.sf_pcs(cs)), cs, pjs, me, isc), Some{cs}, oe.k0(cs, pjs, me, isc)) : {oe.m(_) == True{} : Bool}
  h

def oe.own(+own: Bool, +a: Bool, +j: Nat, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {oe.m(CronServeSafety.sf_render_c(CronServe.sv_claims_out(Sv.finish.own(own, a, j, d, ran, failed, now, pjs, CronServeSafety.sf_pcs(cs))), cs, pjs, me, False{})) == True{} : Bool}:
  match own:
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(Sv.drop_first(d, CronServeSafety.sf_pcs(cs)), cs, pjs, me, False{}), Some{oe.rmf(d, cs)}, oe.df(d, cs, pjs, me, False{})) : {oe.m(_) == True{} : Bool}
      oe.rmf_oe(d, cs, h)
    case False{}:
      oe.keep(cs, pjs, me, False{}, h)

def oe.found(+m: Maybe<&2, Sv.Hit>, +a: Bool, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +me: Nat, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {oe.m(CronServeSafety.sf_render_c(CronServe.sv_claims_out(Sv.finish.found(m, me, a, d, ran, failed, now, pjs, CronServeSafety.sf_pcs(cs))), cs, pjs, me, False{})) == True{} : Bool}:
  match m:
    case None{}:
      oe.keep(cs, pjs, me, False{}, h)
    case Some{x}:
      match x:
        case Sv.Hit{j, o}:
          oe.own(Nat.is_eq(o, me), a, j, d, ran, failed, now, cs, pjs, me, h)

def oe.fin(+b: Bool, +me: Nat, +runs: List<&2, String>, +a: Bool, +d: String, +ran: Bool, +failed: Bool, +now: Nat, +cs: List<&2, CronServeSafety.SfC>, +pjs: List<&2, Sv.JRec>, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {oe.m(CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.finish(b, me, runs, a, d, ran, failed, now, pjs, CronServeSafety.sf_pcs(cs)))), cs, pjs, me, False{})) == True{} : Bool}:
  match b:
    case True{}:
      oe.found(Sv.claim_of(d, CronServeSafety.sf_pcs(cs)), a, d, ran, failed, now, cs, pjs, me, h)
    case False{}:
      oe.keep(cs, pjs, me, False{}, h)

def oe.go(+runs: List<&2, String>, +me: Nat, +a: Bool, +js: List<&2, CronServeSafety.SfJ>, +cs: List<&2, CronServeSafety.SfC>, +op: Sv.Op, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {oe.m(CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(Sv.go(runs, me, a, CronServeSafety.sf_pjs(js), CronServeSafety.sf_pcs(cs), op))), cs, CronServeSafety.sf_pjs(js), me, CronServeSafety.sf_isc(op))) == True{} : Bool}:
  match op:
    case Sv.OClaim{due, now, fresh}:
      oe.claim(Sv.claim(CronServeSafety.sf_pjs(js), 0n, Sv.claim_jobs(CronServeSafety.sf_pcs(cs)), fresh, due, now), a, runs, cs, CronServeSafety.sf_pjs(js), me, h, PCU.cu.pass(CronServeSafety.sf_pjs(js), 0n, Sv.claim_jobs(CronServeSafety.sf_pcs(cs)), fresh, due, now, CronServeSafety.sf_pjs(js), {==}))
    case Sv.ORecover{dead}:
      %Equal.sym(Maybe<&2, List<&2, CronServeSafety.SfC>>, CronServeSafety.sf_render_c(Sv.recover.claims(me, runs, dead, CronServeSafety.sf_pcs(cs)), cs, CronServeSafety.sf_pjs(js), me, False{}), Some{PDC.dc2.filt(me, runs, dead, cs)}, PDC.dc2.f1(me, runs, dead, cs, CronServeSafety.sf_pjs(js), False{})) : {oe.m(_) == True{} : Bool}
      oe.filt_oe(me, runs, dead, cs, h)
    case Sv.OFinish{d, ran, failed, now}:
      oe.fin(Sv.has_str(d, runs), me, runs, a, d, ran, failed, now, cs, CronServeSafety.sf_pjs(js), h)
    case Sv.OCancel{n}:
      oe.keep(cs, CronServeSafety.sf_pjs(js), me, False{}, h)
    case Sv.OResume{n, now}:
      oe.keep(cs, CronServeSafety.sf_pjs(js), me, False{}, h)
    case Sv.OCreate{n, f}:
      oe.keep(cs, CronServeSafety.sf_pjs(js), me, False{}, h)

def oe.base(+a: Bool, +f: CronServeSafety.SfFile, +h: {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(f)) == True{} : Bool}) -> {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(CronServeSafety.sf_base(a, f))) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def oe.written(+w: Bool, +a: Bool, +f: CronServeSafety.SfFile, +mj: Maybe<&2, List<&2, CronServeSafety.SfJ>>, +mc: Maybe<&2, List<&2, CronServeSafety.SfC>>, +hb: {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(CronServeSafety.sf_base(a, f))) == True{} : Bool}, +hm: {oe.m(mc) == True{} : Bool}) -> {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(CronServeSafety.sf_written(w, a, f, mj, mc))) == True{} : Bool}:
  match w:
    case True{}:
      match mj:
        case None{}:
          hb
        case Some{js}:
          match mc:
            case None{}:
              hb
            case Some{cs}:
              hm
    case False{}:
      hb

# Other events
# ------------

def oe.has_raw(+j: Nat, +cs: List<&2, CronServeSafety.SfC>, +x: Nat) -> {CronServeSafety.sf_has_job(j, List.append(&2, CronServeSafety.SfC, cs, [CronServeSafety.SfCR{x}])) == CronServeSafety.sf_has_job(j, cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{d, y, o}:
          Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(y, j), z), CronServeSafety.sf_has_job(j, List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCR{x}])), CronServeSafety.sf_has_job(j, t), oe.has_raw(j, t, x))
        case CronServeSafety.SfCR{z}:
          oe.has_raw(j, t, x)

def oe.raw(+cs: List<&2, CronServeSafety.SfC>, +x: Nat, +h: {CronServeSafety.sf_one_each(cs) == True{} : Bool}) -> {CronServeSafety.sf_one_each(List.append(&2, CronServeSafety.SfC, cs, [CronServeSafety.SfCR{x}])) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case CronServeSafety.SfCK{d, y, o}:
          %Equal.sym(Bool, CronServeSafety.sf_has_job(y, List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCR{x}])), CronServeSafety.sf_has_job(y, t), oe.has_raw(y, t, x)) : {Bool.and(Bool.not(_), CronServeSafety.sf_one_each(List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCR{x}]))) == True{} : Bool}
          LG.lg.and_t(Bool.not(CronServeSafety.sf_has_job(y, t)), CronServeSafety.sf_one_each(List.append(&2, CronServeSafety.SfC, t, [CronServeSafety.SfCR{x}])), LG.lg.and_l(Bool.not(CronServeSafety.sf_has_job(y, t)), CronServeSafety.sf_one_each(t), h), oe.raw(t, x, LG.lg.and_r(Bool.not(CronServeSafety.sf_has_job(y, t)), CronServeSafety.sf_one_each(t), h)))
        case CronServeSafety.SfCR{z}:
          oe.raw(t, x, h)

def oe.rj(+f: CronServeSafety.SfFile, +x: Nat, +h: {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(f)) == True{} : Bool}) -> {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(CronServeSafety.sf_add_job(x, f))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      {==}
    case CronServeSafety.SfTorn{t}:
      h
    case CronServeSafety.SfRead{js, cs}:
      h

def oe.rc(+f: CronServeSafety.SfFile, +x: Nat, +h: {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(f)) == True{} : Bool}) -> {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(CronServeSafety.sf_add_claim(x, f))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      {==}
    case CronServeSafety.SfTorn{t}:
      h
    case CronServeSafety.SfRead{js, cs}:
      oe.raw(cs, x, h)

def oe.fa(+f: CronServeSafety.SfFile, +k: Nat, +g: CS.Fact, +h: {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(f)) == True{} : Bool}) -> {CronServeSafety.sf_one_each(CronServeSafety.sf_claims_of(CronServeSafety.sf_facts(k, g, f))) == True{} : Bool}:
  match f:
    case CronServeSafety.SfMissing{}:
      h
    case CronServeSafety.SfTorn{t}:
      h
    case CronServeSafety.SfRead{js, cs}:
      h

# One event
# ---------

def oe.step(+w: CronServeSafety.SfWorld, +e: CronServeSafety.SfEv, +h: {CronServeSafety.sf_one_each(CronServeSafety.sf_claims(w)) == True{} : Bool}) -> {CronServeSafety.sf_one_each(CronServeSafety.sf_claims(CronServeSafety.sf_step(w, e))) == True{} : Bool}:
  match w:
    case CronServeSafety.SfWorld{+f, +dead, +aside}:
      match e:
        case CronServeSafety.SfUp{+p, +runs, +op}:
          +op2 = CronServeSafety.sf_op(op, dead)
          +g = Sv.go(runs, p, LSf.sg.torn(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), CronServeSafety.sf_pcs(CronServeSafety.sf_claims_of(f)), op2)
          +r = CronServe.sv_reply(Sv.serve(runs, p, CronServeSafety.sf_disk(f), op2))
          %Equal.sym(CronServeSafety.SfWorld, CronServeSafety.sf_apply(r, f, op2, p, dead, aside), CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(r), CronServe.sv_aside(r), f, CronServeSafety.sf_render_j(CronServe.sv_jobs(r), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2)), CronServeSafety.sf_render_c(CronServe.sv_claims_out(r), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2))), dead, CronServeSafety.sf_moved(CronServe.sv_aside(r), f, aside)}, LSf.sg.up(r, f, op2, p, dead, aside)) : {CronServeSafety.sf_one_each(CronServeSafety.sf_claims(_)) == True{} : Bool}
          %Equal.sym(Sv.Served, Sv.serve(runs, p, CronServeSafety.sf_disk(f), op2), g, LSf.sg.serve_go(runs, p, f, op2)) : {CronServeSafety.sf_one_each(CronServeSafety.sf_claims(CronServeSafety.SfWorld{CronServeSafety.sf_written(CronServe.sv_write(CronServe.sv_reply(_)), CronServe.sv_aside(CronServe.sv_reply(_)), f, CronServeSafety.sf_render_j(CronServe.sv_jobs(CronServe.sv_reply(_)), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2)), CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(_)), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2))), dead, CronServeSafety.sf_moved(CronServe.sv_aside(CronServe.sv_reply(_)), f, aside)})) == True{} : Bool}
          oe.written(CronServe.sv_write(CronServe.sv_reply(g)), CronServe.sv_aside(CronServe.sv_reply(g)), f, CronServeSafety.sf_render_j(CronServe.sv_jobs(CronServe.sv_reply(g)), CronServeSafety.sf_jobs(f), CronServeSafety.sf_made(op2)), CronServeSafety.sf_render_c(CronServe.sv_claims_out(CronServe.sv_reply(g)), CronServeSafety.sf_claims_of(f), CronServeSafety.sf_pjs(CronServeSafety.sf_jobs(f)), p, CronServeSafety.sf_isc(op2)), oe.base(CronServe.sv_aside(CronServe.sv_reply(g)), f, h), oe.go(runs, p, LSf.sg.torn(f), CronServeSafety.sf_jobs(f), CronServeSafety.sf_claims_of(f), op2, h))
        case CronServeSafety.SfDie{q}:
          h
        case CronServeSafety.SfRawJob{+x}:
          oe.rj(f, x, h)
        case CronServeSafety.SfRawClaim{+x}:
          oe.rc(f, x, h)
        case CronServeSafety.SfFacts{+k, +g}:
          oe.fa(f, k, g, h)
        case CronServeSafety.SfCorrupt{x}:
          {==}

def CronServeSafety.cron_serve_one_claim_per_job(evs):
  match evs:
    case Nil{}:
      {==}
    case +e <> +t:
      oe.step(CronServeSafety.sf_run(t), e, CronServeSafety.cron_serve_one_claim_per_job(t))
