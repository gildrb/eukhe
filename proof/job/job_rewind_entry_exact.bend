# eukhe: the proof of LAW job_rewind_entry_exact
# The entry answers a value only after it read a target, a count and as
# many jobs, with nothing left; each part read is spelled and fits
# (base/entry.bend), so the input is the spelled request.

import Base
import ../../bend/ffi_job.bend as FJb
import ../../bend/ffi_job_rewind.bend as FJr
import ../../bend/job.bend as Jb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job.bend as Job
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./base/entry.bend as JER

def jrx.G(s: String) -> Type:
  Sigma<&1, &1, Maybe<&2, Nat>, tg => Sigma<&1, &1, List<&2, Jb.Seen>, js => {Job.rw_req_fits(tg, js) == True{} : Bool} & {s == Job.rw_spell_req(tg, js) : String}>>

def jrx.fin(-s: String, +tg: Maybe<&2, Nat>, -s1: String, +n: Nat, -s2: String, +js: List<&2, Jb.Seen>, q: String, ft: {LawsBase.wire_mfits(tg) == True{} : Bool}, e1: {s == Job.rw_spell_commit(tg, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, e2: {s1 == Wr.put_nat(n, s2) : String}, +el: {List.length(&2, Jb.Seen, js) == n : Nat}, fj: {Job.rw_seens_fit(js) == True{} : Bool}, e3: {s2 == Job.rw_spell_seens(js, q) : String}, ok: {LawsBase.wire_opens_err(FJr.run.end(Wr.end(q), tg, js)) == False{} : Bool}) -> jrx.G(s):
  match q:
    case SNil{}:
      +L = List.length(&2, Jb.Seen, js)
      +X = Job.rw_spell_seens(js, "")
      +fl = Equal.trans(Bool, LawsBase.wire_fits(L), LawsBase.wire_fits(n), True{}, Equal.cong(Nat, Bool, m => LawsBase.wire_fits(m), L, n, el), fn)
      +fits = JER.jer.and_tt(LawsBase.wire_mfits(tg), Bool.and(LawsBase.wire_fits(L), Job.rw_seens_fit(js)), ft, JER.jer.and_tt(LawsBase.wire_fits(L), Job.rw_seens_fit(js), fl, fj))
      +a = JER.jer.then(z => Wr.put_nat(n, z), s1, s2, X, e2, e3)
      +b = Equal.trans(String, s1, Wr.put_nat(n, X), Wr.put_nat(L, X), a, Equal.cong(Nat, String, m => Wr.put_nat(m, X), n, L, Equal.sym(Nat, L, n, el)))
      (tg, (js, (fits, JER.jer.then(z => Job.rw_spell_commit(tg, z), s, s1, Wr.put_nat(L, X), e1, b))))
    case SCon{x, y}:
      LLogicLogic.pf.absurd_tf(jrx.G(s), ok)

def jrx.list(-s: String, +tg: Maybe<&2, Nat>, -s1: String, +n: Nat, -s2: String, ft: {LawsBase.wire_mfits(tg) == True{} : Bool}, e1: {s == Job.rw_spell_commit(tg, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, e2: {s1 == Wr.put_nat(n, s2) : String}, d: Wr.Dec<List<&2, Jb.Seen>>, rp: JER.jer.SeensRP(s2, n, d), ok: {LawsBase.wire_opens_err(FJr.run.jobs(tg, d)) == False{} : Bool}) -> jrx.G(s):
  match d:
    case Wr.Got{+js, +q}:
      (el, (fj, e3)) = rp
      jrx.fin(s, tg, s1, n, s2, js, q, ft, e1, fn, e2, el, fj, e3, ok)
    case Wr.Bad{}:
      LLogicLogic.pf.absurd_tf(jrx.G(s), ok)

def jrx.count(-s: String, +tg: Maybe<&2, Nat>, +s1: String, ft: {LawsBase.wire_mfits(tg) == True{} : Bool}, e1: {s == Job.rw_spell_commit(tg, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FJr.run.jobs(tg, FJr.get_seens(d))) == False{} : Bool}) -> jrx.G(s):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      jrx.list(s, tg, s1, n, s2, ft, e1, Wire.wire_nat_decoded_fits(s1, n, s2, e), Wire.wire_nat_exact(s1, n, s2, e), FJr.get_seens(Wr.Got{n, s2}), JER.jer.seens(n, s2), ok)
    case Wr.Bad{}:
      LLogicLogic.pf.absurd_tf(jrx.G(s), ok)

def jrx.top(-s: String, d: Wr.Dec<Maybe<&2, Nat>>, rp: JER.jer.CommitRP(s, d), ok: {LawsBase.wire_opens_err(FJr.run(d)) == False{} : Bool}) -> jrx.G(s):
  match d:
    case Wr.Got{+tg, +s1}:
      (ft, e1) = rp
      jrx.count(s, tg, s1, ft, e1, Wr.get_nat(s1), {==}, ok)
    case Wr.Bad{}:
      LLogicLogic.pf.absurd_tf(jrx.G(s), ok)

def Job.job_rewind_entry_exact(s, ok):
  jrx.top(s, FJr.get_commit(s), JER.jer.commit(s), ok)
