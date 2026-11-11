# eukhe: the proof of LAW goal_entry_reads_only_requests
# PROOF: whatever each stage of the entry reads is the spelling of what it
# read, then its rest, and fits the wire (the wire's exactness laws, tag by
# tag: an unknown prior tag is Bad); each stage carries the input spelled up
# to its field, so an answer that is not the malformed error comes from a
# request read whole, nothing left. Every Bad answers the error, which the
# premise rules out.

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def gro.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# The prior
# ---------

def gro.Prior(s: String, d: Wr.Dec<Maybe<&2, Pr.Prior>>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == Progress.gs_spell_prior(p, r) : String} & {Progress.wire_prior_fits(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gro.prior.w(+s: String, +sv: Nat, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(sv, s1)) : String}, fs: {LawsBase.wire_fits(sv) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> gro.Prior(s, FPr.get_prior.w(sv, d)):
  match d:
    case Wr.Got{+w, +s2}:
      +ee = ed
      (gro.step(z => Wr.put_nat(1n, Wr.put_nat(sv, z)), s, s1, Wr.put_nat(w, s2), pre, Wire.wire_nat_exact(s1, w, s2, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(sv), LawsBase.wire_fits(w), fs, Wire.wire_nat_decoded_fits(s1, w, s2, ee)))
    case Wr.Bad{}:
      Unit{}

def gro.prior.s(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> gro.Prior(s, FPr.get_prior.s(d)):
  match d:
    case Wr.Got{+sv, +s1}:
      +ee = ed
      gro.prior.w(s, sv, s1, gro.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(sv, s1), pre, Wire.wire_nat_exact(s0, sv, s1, ee)), Wire.wire_nat_decoded_fits(s0, sv, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# whatever the entry's prior decoder reads is a spelled prior that fits,
# then the rest
def gro.prior(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> gro.Prior(s, FPr.get_prior.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n+p:
          match p:
            case 0n:
              gro.prior.s(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
            case 1n+q:
              Unit{}
    case Wr.Bad{}:
      Unit{}

# The request
# -----------

def gro.G(s: String) -> Type:
  Sigma<&1, &1, Progress.gs.Req, q => {(s, Progress.gs_fits(q)) == (Progress.gs_spell_req(q), True{}) : String & Bool}>

def gro.pair(+s: String, +q: Progress.gs.Req, e: {s == Progress.gs_spell_req(q) : String}, f: {Progress.gs_fits(q) == True{} : Bool}) -> {(s, Progress.gs_fits(q)) == (Progress.gs_spell_req(q), True{}) : String & Bool}:
  %Equal.sym(String, s, Progress.gs_spell_req(q), e) : {(_, Progress.gs_fits(q)) == (Progress.gs_spell_req(q), True{}) : String & Bool}
  %Equal.sym(Bool, Progress.gs_fits(q), True{}, f) : {(Progress.gs_spell_req(q), _) == (Progress.gs_spell_req(q), True{}) : String & Bool}
  {==}

# the end check: nothing left is the request, anything left the error
def gro.end(+s: String, +t: Nat, +cap: Nat, +p: Maybe<&2, Pr.Prior>, +work: Nat, r: String, pre: {s == Wr.put_nat(t, Wr.put_nat(cap, Progress.gs_spell_prior(p, Wr.put_nat(work, r)))) : String}, f: {Progress.gs_fits(Progress.gs.Req{t, cap, p, work}) == True{} : Bool}, other: {String.eq(FPr.run.end(Wr.end(r), t, cap, p, work), Wr.err("progress: malformed request")) == False{} : Bool}) -> gro.G(s):
  match r:
    case SNil{}:
      (Progress.gs.Req{t, cap, p, work}, gro.pair(s, Progress.gs.Req{t, cap, p, work}, pre, f))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(gro.G(s), other)

def gro.work(+s: String, +t: Nat, +cap: Nat, +p: Maybe<&2, Pr.Prior>, +s3: String, pre: {s == Wr.put_nat(t, Wr.put_nat(cap, Progress.gs_spell_prior(p, s3))) : String}, +ft: {LawsBase.wire_fits(t) == True{} : Bool}, +fc: {LawsBase.wire_fits(cap) == True{} : Bool}, +fp: {Progress.wire_prior_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}, other: {String.eq(FPr.run.work(t, cap, p, d), Wr.err("progress: malformed request")) == False{} : Bool}) -> gro.G(s):
  match d:
    case Wr.Got{+work, +s4}:
      +ee = ed
      +fw = Wire.wire_nat_decoded_fits(s3, work, s4, ee)
      +f = LAWireSpell.ws_and_tt(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(cap), Bool.and(Progress.wire_prior_fits(p), LawsBase.wire_fits(work))), ft, LAWireSpell.ws_and_tt(LawsBase.wire_fits(cap), Bool.and(Progress.wire_prior_fits(p), LawsBase.wire_fits(work)), fc, LAWireSpell.ws_and_tt(Progress.wire_prior_fits(p), LawsBase.wire_fits(work), fp, fw)))
      gro.end(s, t, cap, p, work, s4, gro.step(z => Wr.put_nat(t, Wr.put_nat(cap, Progress.gs_spell_prior(p, z))), s, s3, Wr.put_nat(work, s4), pre, Wire.wire_nat_exact(s3, work, s4, ee)), f, other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gro.G(s), other)

def gro.prior_stage(+s: String, +t: Nat, +cap: Nat, +s2: String, pre: {s == Wr.put_nat(t, Wr.put_nat(cap, s2)) : String}, +ft: {LawsBase.wire_fits(t) == True{} : Bool}, +fc: {LawsBase.wire_fits(cap) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Pr.Prior>>, inv: gro.Prior(s2, d), other: {String.eq(FPr.run.prior(t, cap, d), Wr.err("progress: malformed request")) == False{} : Bool}) -> gro.G(s):
  match d:
    case Wr.Got{+p, +s3}:
      (e, fp) = inv
      gro.work(s, t, cap, p, s3, gro.step(z => Wr.put_nat(t, Wr.put_nat(cap, z)), s, s2, Progress.gs_spell_prior(p, s3), pre, e), ft, fc, fp, Wr.get_nat(s3), {==}, other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gro.G(s), other)

def gro.cap(+s: String, +t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}, +ft: {LawsBase.wire_fits(t) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, other: {String.eq(FPr.run.cap(t, d), Wr.err("progress: malformed request")) == False{} : Bool}) -> gro.G(s):
  match d:
    case Wr.Got{+cap, +s2}:
      +ee = ed
      gro.prior_stage(s, t, cap, s2, gro.step(z => Wr.put_nat(t, z), s, s1, Wr.put_nat(cap, s2), pre, Wire.wire_nat_exact(s1, cap, s2, ee)), ft, Wire.wire_nat_decoded_fits(s1, cap, s2, ee), FPr.get_prior(s2), gro.prior(s2, Wr.get_nat(s2), {==}), other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gro.G(s), other)

def gro.t(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, other: {String.eq(FPr.run.t(d), Wr.err("progress: malformed request")) == False{} : Bool}) -> gro.G(s):
  match d:
    case Wr.Got{+t, +s1}:
      +ee = ed
      gro.cap(s, t, s1, Wire.wire_nat_exact(s, t, s1, ee), Wire.wire_nat_decoded_fits(s, t, s1, ee), Wr.get_nat(s1), {==}, other)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gro.G(s), other)

def Progress.goal_entry_reads_only_requests(s, other):
  gro.t(s, Wr.get_nat(s), {==}, other)
