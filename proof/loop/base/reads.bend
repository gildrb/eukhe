# eukhe: what each decoder answer of the loop entry says about its input
# (le.ci_*): a Got answer comes from the spelling of the value, which fits
# the wire. Each stage is a wire value its exactness law inverts
# (wire_nat_exact, wire_str_exact, wire_bool_exact), threading `pre`, the
# input spelled so far (le.into); a decoded value fits
# (wire_nat_decoded_fits, wire_str_decoded_fits). Used by
# loop_ffi_reads_only_requests and loop_ffi_malformed_unless_request.

import Base
import ../../../bend/loop.bend as Lp
import ../../../bend/ffi_loop.bend as FLp
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/loop/entry.bend as LoopEntry
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/base/spell.bend as LAWireSpell

# ---- threading ----

# the input spelled so far, one value further: s is f of a, and a is b
def le.into(-s: String, -f: String -> String, -a: String, -b: String, pre: {s == f(a) : String}, e: {a == b : String}) -> {s == f(b) : String}:
  %e : {s == f(_) : String}
  pre

# ---- primitives ----

def le.ci_nat(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{+n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.ci_nat_at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> le.ci_nat(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e = ed
      (Wire.wire_nat_exact(s, n, r, e), Wire.wire_nat_decoded_fits(s, n, r, e))
    case Wr.Bad{}:
      Unit{}

def le.ci_nat_all(+s: String) -> le.ci_nat(s, Wr.get_nat(s)):
  le.ci_nat_at(s, Wr.get_nat(s), {==})

def le.ci_str(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+t, r}:
      {s == Wr.put_str(t, r) : String} & {LawsBase.wire_fits(String.length(t)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.ci_str_at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> le.ci_str(s, d):
  match d:
    case Wr.Got{+t, +r}:
      +e = ed
      (Wire.wire_str_exact(s, t, r, e), Wire.wire_str_decoded_fits(s, t, r, e))
    case Wr.Bad{}:
      Unit{}

def le.ci_str_all(+s: String) -> le.ci_str(s, Wr.get_str(s)):
  le.ci_str_at(s, Wr.get_str(s), {==})

def le.ci_bool(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def le.ci_bool_at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> le.ci_bool(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def le.ci_bool_all(+s: String) -> le.ci_bool(s, Wr.get_bool(s)):
  le.ci_bool_at(s, Wr.get_bool(s), {==})

# ---- Maybe<Nat>, Maybe<String> ----

def le.ci_mnat(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+m, r}:
      {s == LoopEntry.lp_spell_mnat(m, r) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.cm_some(-s: String, -s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, cn: le.ci_nat(s1, d)) -> le.ci_mnat(s, FLp.get_mnat.some(d)):
  match d:
    case Wr.Got{+x, +s2}:
      (e2, f) = cn
      (le.into(s, z => Wr.put_nat(1n, z), s1, Wr.put_nat(x, s2), e, e2), f)
    case Wr.Bad{}:
      Unit{}

def le.cm_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_mnat(s, FLp.get_mnat.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      le.cm_some(s, s1, e, Wr.get_nat(s1), le.ci_nat_all(s1))
    case 2n+x:
      Unit{}

def le.cm_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_mnat(s, FLp.get_mnat.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.cm_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_mnat_all(+s: String) -> le.ci_mnat(s, FLp.get_mnat(s)):
  le.cm_go(s, Wr.get_nat(s), le.ci_nat_all(s))

def le.ci_mstr(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{+m, r}:
      {s == LoopEntry.lp_spell_mstr(m, r) : String} & {LoopEntry.lp_mstr_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.ct_some(-s: String, -s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ct: le.ci_str(s1, d)) -> le.ci_mstr(s, FLp.get_mstr.some(d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e2, f) = ct
      (le.into(s, z => Wr.put_nat(1n, z), s1, Wr.put_str(t, s2), e, e2), f)
    case Wr.Bad{}:
      Unit{}

def le.ct_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_mstr(s, FLp.get_mstr.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      le.ct_some(s, s1, e, Wr.get_str(s1), le.ci_str_all(s1))
    case 2n+x:
      Unit{}

def le.ct_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_mstr(s, FLp.get_mstr.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.ct_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_mstr_all(+s: String) -> le.ci_mstr(s, FLp.get_mstr(s)):
  le.ct_go(s, Wr.get_nat(s), le.ci_nat_all(s))

# ---- the condition ----

def le.ci_cond(s: String, d: Wr.Dec<Lp.Cond>) -> Type:
  match d:
    case Wr.Got{+c, r}:
      {s == LoopEntry.lp_spell_cond(c, r) : String} & {LoopEntry.lp_cond_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.cc_until(-s: String, -s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ct: le.ci_str(s1, d)) -> le.ci_cond(s, FLp.get_cond.until(d)):
  match d:
    case Wr.Got{+cmd, +s2}:
      (e2, f) = ct
      (le.into(s, z => Wr.put_nat(1n, z), s1, Wr.put_str(cmd, s2), e, e2), f)
    case Wr.Bad{}:
      Unit{}

def le.cc_while(-s: String, -s1: String, e: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, ct: le.ci_str(s1, d)) -> le.ci_cond(s, FLp.get_cond.while(d)):
  match d:
    case Wr.Got{+cmd, +s2}:
      (e2, f) = ct
      (le.into(s, z => Wr.put_nat(2n, z), s1, Wr.put_str(cmd, s2), e, e2), f)
    case Wr.Bad{}:
      Unit{}

def le.cc_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_cond(s, FLp.get_cond.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      le.cc_until(s, s1, e, Wr.get_str(s1), le.ci_str_all(s1))
    case 2n:
      le.cc_while(s, s1, e, Wr.get_str(s1), le.ci_str_all(s1))
    case 3n+x:
      Unit{}

def le.cc_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_cond(s, FLp.get_cond.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.cc_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_cond_all(+s: String) -> le.ci_cond(s, FLp.get_cond(s)):
  le.cc_go(s, Wr.get_nat(s), le.ci_nat_all(s))

# ---- the evidence ----

def le.ci_evid(s: String, d: Wr.Dec<Lp.Evid>) -> Type:
  match d:
    case Wr.Got{+v, r}:
      {s == LoopEntry.lp_spell_evid(v, r) : String} & {LoopEntry.lp_evid_fits(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.cv_code(-s: String, -s1: String, e: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, cn: le.ci_nat(s1, d)) -> le.ci_evid(s, FLp.get_evid.code(d)):
  match d:
    case Wr.Got{+code, +s2}:
      (e2, f) = cn
      (le.into(s, z => Wr.put_nat(0n, z), s1, Wr.put_nat(code, s2), e, e2), f)
    case Wr.Bad{}:
      Unit{}

def le.cv_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_evid(s, FLp.get_evid.tag(t, s1)):
  match t:
    case 0n:
      le.cv_code(s, s1, e, Wr.get_nat(s1), le.ci_nat_all(s1))
    case 1n:
      (e, {==})
    case 2n:
      (e, {==})
    case 3n:
      (e, {==})
    case 4n:
      (e, {==})
    case 5n+x:
      Unit{}

def le.cv_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_evid(s, FLp.get_evid.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.cv_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_evid_all(+s: String) -> le.ci_evid(s, FLp.get_evid(s)):
  le.cv_go(s, Wr.get_nat(s), le.ci_nat_all(s))

# ---- the end and the phase ----

def le.ci_end(s: String, d: Wr.Dec<Lp.End>) -> Type:
  match d:
    case Wr.Got{w, r}:
      {s == LoopEntry.lp_spell_end(w, r) : String}
    case Wr.Bad{}:
      Unit

def le.cn_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_end(s, FLp.get_end.tag(t, s1)):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
    case 4n:
      e
    case 5n:
      e
    case 6n:
      e
    case 7n+x:
      Unit{}

def le.cn_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_end(s, FLp.get_end.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.cn_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_end_all(+s: String) -> le.ci_end(s, FLp.get_end(s)):
  le.cn_go(s, Wr.get_nat(s), le.ci_nat_all(s))

def le.ci_phase(s: String, d: Wr.Dec<Lp.Phase>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == LoopEntry.lp_spell_phase(p, r) : String}
    case Wr.Bad{}:
      Unit

def le.cp_ended(-s: String, -s1: String, e: {s == Wr.put_nat(5n, s1) : String}, d: Wr.Dec<Lp.End>, cw: le.ci_end(s1, d)) -> le.ci_phase(s, FLp.get_phase.ended(d)):
  match d:
    case Wr.Got{+w, +s2}:
      le.into(s, z => Wr.put_nat(5n, z), s1, LoopEntry.lp_spell_end(w, s2), e, cw)
    case Wr.Bad{}:
      Unit{}

def le.cp_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_phase(s, FLp.get_phase.tag(t, s1)):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
    case 4n:
      e
    case 5n:
      le.cp_ended(s, s1, e, FLp.get_end(s1), le.ci_end_all(s1))
    case 6n+x:
      Unit{}

def le.cp_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_phase(s, FLp.get_phase.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.cp_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_phase_all(+s: String) -> le.ci_phase(s, FLp.get_phase(s)):
  le.cp_go(s, Wr.get_nat(s), le.ci_nat_all(s))

# ---- the last evidence ----

def le.ci_last(s: String, d: Wr.Dec<Lp.Last>) -> Type:
  match d:
    case Wr.Got{+z, r}:
      {s == LoopEntry.lp_spell_last(z, r) : String} & {LoopEntry.lp_last_fits(z) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.cl_ev(-s: String, -at: Nat, -s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(at, s1)) : String}, fa: {LawsBase.wire_fits(at) == True{} : Bool},
  d: Wr.Dec<Lp.Evid>, cv: le.ci_evid(s1, d)) -> le.ci_last(s, FLp.get_last.ev(at, d)):
  match d:
    case Wr.Got{+ev, +s2}:
      (e, f) = cv
      (le.into(s, z => Wr.put_nat(1n, Wr.put_nat(at, z)), s1, LoopEntry.lp_spell_evid(ev, s2), pre, e),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(at), LoopEntry.lp_evid_fits(ev), fa, f))
    case Wr.Bad{}:
      Unit{}

def le.cl_at(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, cn: le.ci_nat(s1, d)) -> le.ci_last(s, FLp.get_last.at(d)):
  match d:
    case Wr.Got{+at, +s2}:
      (e, f) = cn
      le.cl_ev(s, at, s2, le.into(s, z => Wr.put_nat(1n, z), s1, Wr.put_nat(at, s2), pre, e), f, FLp.get_evid(s2), le.ci_evid_all(s2))
    case Wr.Bad{}:
      Unit{}

def le.cl_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_last(s, FLp.get_last.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      le.cl_at(s, s1, e, Wr.get_nat(s1), le.ci_nat_all(s1))
    case 2n+x:
      Unit{}

def le.cl_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_last(s, FLp.get_last.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.cl_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_last_all(+s: String) -> le.ci_last(s, FLp.get_last(s)):
  le.cl_go(s, Wr.get_nat(s), le.ci_nat_all(s))

# ---- the state ----

def le.ci_st(s: String, d: Wr.Dec<Lp.St>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == LoopEntry.lp_spell_st(x, r) : String} & {LoopEntry.lp_st_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.cs_last(-s0: String, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -s7: String,
  pre: {s0 == LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, LoopEntry.lp_spell_cond(c, Wr.put_str(b, Wr.put_nat(f, s7))))))) : String},
  fi: {LawsBase.wire_fits(i) == True{} : Bool}, fl: {LawsBase.wire_mfits(l) == True{} : Bool}, fd: {LawsBase.wire_mfits(d) == True{} : Bool},
  fc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, ff: {LawsBase.wire_fits(f) == True{} : Bool},
  r: Wr.Dec<Lp.Last>, cz: le.ci_last(s7, r)) -> le.ci_st(s0, FLp.get_st.last(p, i, l, d, c, b, f, r)):
  match r:
    case Wr.Got{+z, +s8}:
      (e, fz) = cz
      (le.into(s0, y => LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, LoopEntry.lp_spell_cond(c, Wr.put_str(b, Wr.put_nat(f, y))))))), s7, LoopEntry.lp_spell_last(z, s8), pre, e),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_mfits(l), Bool.and(LawsBase.wire_mfits(d), Bool.and(LoopEntry.lp_cond_fits(c), Bool.and(LawsBase.wire_fits(String.length(b)), Bool.and(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(z)))))), fi,
          LAWireSpell.ws_and_tt(LawsBase.wire_mfits(l), Bool.and(LawsBase.wire_mfits(d), Bool.and(LoopEntry.lp_cond_fits(c), Bool.and(LawsBase.wire_fits(String.length(b)), Bool.and(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(z))))), fl,
            LAWireSpell.ws_and_tt(LawsBase.wire_mfits(d), Bool.and(LoopEntry.lp_cond_fits(c), Bool.and(LawsBase.wire_fits(String.length(b)), Bool.and(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(z)))), fd,
              LAWireSpell.ws_and_tt(LoopEntry.lp_cond_fits(c), Bool.and(LawsBase.wire_fits(String.length(b)), Bool.and(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(z))), fc,
                LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(b)), Bool.and(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(z)), fb,
                  LAWireSpell.ws_and_tt(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(z), ff, fz)))))))
    case Wr.Bad{}:
      Unit{}

def le.cs_fails(-s0: String, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -s6: String,
  pre: {s0 == LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, LoopEntry.lp_spell_cond(c, Wr.put_str(b, s6)))))) : String},
  fi: {LawsBase.wire_fits(i) == True{} : Bool}, fl: {LawsBase.wire_mfits(l) == True{} : Bool}, fd: {LawsBase.wire_mfits(d) == True{} : Bool},
  fc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool},
  r: Wr.Dec<Nat>, cn: le.ci_nat(s6, r)) -> le.ci_st(s0, FLp.get_st.fails(p, i, l, d, c, b, r)):
  match r:
    case Wr.Got{+f, +s7}:
      (e, ff) = cn
      le.cs_last(s0, p, i, l, d, c, b, f, s7,
        le.into(s0, y => LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, LoopEntry.lp_spell_cond(c, Wr.put_str(b, y)))))), s6, Wr.put_nat(f, s7), pre, e),
        fi, fl, fd, fc, fb, ff, FLp.get_last(s7), le.ci_last_all(s7))
    case Wr.Bad{}:
      Unit{}

def le.cs_body(-s0: String, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -s5: String,
  pre: {s0 == LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, LoopEntry.lp_spell_cond(c, s5))))) : String},
  fi: {LawsBase.wire_fits(i) == True{} : Bool}, fl: {LawsBase.wire_mfits(l) == True{} : Bool}, fd: {LawsBase.wire_mfits(d) == True{} : Bool},
  fc: {LoopEntry.lp_cond_fits(c) == True{} : Bool},
  r: Wr.Dec<String>, ct: le.ci_str(s5, r)) -> le.ci_st(s0, FLp.get_st.body(p, i, l, d, c, r)):
  match r:
    case Wr.Got{+b, +s6}:
      (e, fb) = ct
      le.cs_fails(s0, p, i, l, d, c, b, s6,
        le.into(s0, y => LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, LoopEntry.lp_spell_cond(c, y))))), s5, Wr.put_str(b, s6), pre, e),
        fi, fl, fd, fc, fb, Wr.get_nat(s6), le.ci_nat_all(s6))
    case Wr.Bad{}:
      Unit{}

def le.cs_cond(-s0: String, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -s4: String,
  pre: {s0 == LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, s4)))) : String},
  fi: {LawsBase.wire_fits(i) == True{} : Bool}, fl: {LawsBase.wire_mfits(l) == True{} : Bool}, fd: {LawsBase.wire_mfits(d) == True{} : Bool},
  r: Wr.Dec<Lp.Cond>, cc: le.ci_cond(s4, r)) -> le.ci_st(s0, FLp.get_st.cond(p, i, l, d, r)):
  match r:
    case Wr.Got{+c, +s5}:
      (e, fc) = cc
      le.cs_body(s0, p, i, l, d, c, s5,
        le.into(s0, y => LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, LoopEntry.lp_spell_mnat(d, y)))), s4, LoopEntry.lp_spell_cond(c, s5), pre, e),
        fi, fl, fd, fc, Wr.get_str(s5), le.ci_str_all(s5))
    case Wr.Bad{}:
      Unit{}

def le.cs_deadline(-s0: String, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -s3: String,
  pre: {s0 == LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, s3))) : String},
  fi: {LawsBase.wire_fits(i) == True{} : Bool}, fl: {LawsBase.wire_mfits(l) == True{} : Bool},
  r: Wr.Dec<Maybe<&2, Nat>>, cm: le.ci_mnat(s3, r)) -> le.ci_st(s0, FLp.get_st.deadline(p, i, l, r)):
  match r:
    case Wr.Got{+d, +s4}:
      (e, fd) = cm
      le.cs_cond(s0, p, i, l, d, s4,
        le.into(s0, y => LoopEntry.lp_spell_phase(p, Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, y))), s3, LoopEntry.lp_spell_mnat(d, s4), pre, e),
        fi, fl, fd, FLp.get_cond(s4), le.ci_cond_all(s4))
    case Wr.Bad{}:
      Unit{}

def le.cs_left(-s0: String, -p: Lp.Phase, -i: Nat, -s2: String,
  pre: {s0 == LoopEntry.lp_spell_phase(p, Wr.put_nat(i, s2)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool},
  r: Wr.Dec<Maybe<&2, Nat>>, cm: le.ci_mnat(s2, r)) -> le.ci_st(s0, FLp.get_st.left(p, i, r)):
  match r:
    case Wr.Got{+l, +s3}:
      (e, fl) = cm
      le.cs_deadline(s0, p, i, l, s3,
        le.into(s0, y => LoopEntry.lp_spell_phase(p, Wr.put_nat(i, y)), s2, LoopEntry.lp_spell_mnat(l, s3), pre, e),
        fi, fl, FLp.get_mnat(s3), le.ci_mnat_all(s3))
    case Wr.Bad{}:
      Unit{}

def le.cs_iter(-s0: String, -p: Lp.Phase, -s1: String, pre: {s0 == LoopEntry.lp_spell_phase(p, s1) : String},
  r: Wr.Dec<Nat>, cn: le.ci_nat(s1, r)) -> le.ci_st(s0, FLp.get_st.iter(p, r)):
  match r:
    case Wr.Got{+i, +s2}:
      (e, fi) = cn
      le.cs_left(s0, p, i, s2,
        le.into(s0, y => LoopEntry.lp_spell_phase(p, y), s1, Wr.put_nat(i, s2), pre, e),
        fi, FLp.get_mnat(s2), le.ci_mnat_all(s2))
    case Wr.Bad{}:
      Unit{}

def le.cs_phase(-s0: String, r: Wr.Dec<Lp.Phase>, cp: le.ci_phase(s0, r)) -> le.ci_st(s0, FLp.get_st.phase(r)):
  match r:
    case Wr.Got{+p, +s1}:
      le.cs_iter(s0, p, s1, cp, Wr.get_nat(s1), le.ci_nat_all(s1))
    case Wr.Bad{}:
      Unit{}

# every state the reader reads is spelled, and fits
def le.ci_st_all(+s: String) -> le.ci_st(s, FLp.get_st(s)):
  le.cs_phase(s, FLp.get_phase(s), le.ci_phase_all(s))

# ---- limits and outcomes ----

def le.ci_limit(s: String, d: Wr.Dec<Lp.Limit>) -> Type:
  match d:
    case Wr.Got{+lim, r}:
      {s == LoopEntry.lp_spell_limit(lim, r) : String} & {LoopEntry.lp_limit_fits(lim) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.ck_count(-s: String, -s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, cn: le.ci_nat(s1, d)) -> le.ci_limit(s, FLp.get_limit.count(d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e2, f) = cn
      (le.into(s, z => Wr.put_nat(1n, z), s1, Wr.put_nat(n, s2), e, e2), f)
    case Wr.Bad{}:
      Unit{}

def le.ck_span(-s: String, -s1: String, e: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, cn: le.ci_nat(s1, d)) -> le.ci_limit(s, FLp.get_limit.span(d)):
  match d:
    case Wr.Got{+ms, +s2}:
      (e2, f) = cn
      (le.into(s, z => Wr.put_nat(2n, z), s1, Wr.put_nat(ms, s2), e, e2), f)
    case Wr.Bad{}:
      Unit{}

def le.ck_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_limit(s, FLp.get_limit.tag(t, s1)):
  match t:
    case 0n:
      (e, {==})
    case 1n:
      le.ck_count(s, s1, e, Wr.get_nat(s1), le.ci_nat_all(s1))
    case 2n:
      le.ck_span(s, s1, e, Wr.get_nat(s1), le.ci_nat_all(s1))
    case 3n+x:
      Unit{}

def le.ck_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_limit(s, FLp.get_limit.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.ck_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_limit_all(+s: String) -> le.ci_limit(s, FLp.get_limit(s)):
  le.ck_go(s, Wr.get_nat(s), le.ci_nat_all(s))

def le.ci_out(s: String, d: Wr.Dec<Lp.Out>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == LoopEntry.lp_spell_out(o, r) : String}
    case Wr.Bad{}:
      Unit

def le.co_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_out(s, FLp.get_out.tag(t, s1)):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n+x:
      Unit{}

def le.co_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_out(s, FLp.get_out.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.co_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

def le.ci_out_all(+s: String) -> le.ci_out(s, FLp.get_out(s)):
  le.co_go(s, Wr.get_nat(s), le.ci_nat_all(s))

# ---- events ----

def le.ci_ev(s: String, d: Wr.Dec<Lp.Ev>) -> Type:
  match d:
    case Wr.Got{+e, r}:
      {s == LoopEntry.lp_spell_ev(e, r) : String} & {LoopEntry.lp_ev_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.ce_enter_now(-s: String, -lim: Lp.Limit, -c: Lp.Cond, -pr: Maybe<&2, String>, -s4: String,
  pre: {s == Wr.put_nat(0n, LoopEntry.lp_spell_limit(lim, LoopEntry.lp_spell_cond(c, LoopEntry.lp_spell_mstr(pr, s4)))) : String},
  fl: {LoopEntry.lp_limit_fits(lim) == True{} : Bool}, fc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, fp: {LoopEntry.lp_mstr_fits(pr) == True{} : Bool},
  d: Wr.Dec<Nat>, cn: le.ci_nat(s4, d)) -> le.ci_ev(s, FLp.get_ev.enter.now(lim, c, pr, d)):
  match d:
    case Wr.Got{+now, +s5}:
      (e, fn) = cn
      (le.into(s, y => Wr.put_nat(0n, LoopEntry.lp_spell_limit(lim, LoopEntry.lp_spell_cond(c, LoopEntry.lp_spell_mstr(pr, y)))), s4, Wr.put_nat(now, s5), pre, e),
        LAWireSpell.ws_and_tt(LoopEntry.lp_limit_fits(lim), Bool.and(LoopEntry.lp_cond_fits(c), Bool.and(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now))), fl,
          LAWireSpell.ws_and_tt(LoopEntry.lp_cond_fits(c), Bool.and(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now)), fc,
            LAWireSpell.ws_and_tt(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now), fp, fn))))
    case Wr.Bad{}:
      Unit{}

def le.ce_enter_prompt(-s: String, -lim: Lp.Limit, -c: Lp.Cond, -s3: String,
  pre: {s == Wr.put_nat(0n, LoopEntry.lp_spell_limit(lim, LoopEntry.lp_spell_cond(c, s3))) : String},
  fl: {LoopEntry.lp_limit_fits(lim) == True{} : Bool}, fc: {LoopEntry.lp_cond_fits(c) == True{} : Bool},
  d: Wr.Dec<Maybe<&2, String>>, cm: le.ci_mstr(s3, d)) -> le.ci_ev(s, FLp.get_ev.enter.prompt(lim, c, d)):
  match d:
    case Wr.Got{+pr, +s4}:
      (e, fp) = cm
      le.ce_enter_now(s, lim, c, pr, s4,
        le.into(s, y => Wr.put_nat(0n, LoopEntry.lp_spell_limit(lim, LoopEntry.lp_spell_cond(c, y))), s3, LoopEntry.lp_spell_mstr(pr, s4), pre, e),
        fl, fc, fp, Wr.get_nat(s4), le.ci_nat_all(s4))
    case Wr.Bad{}:
      Unit{}

def le.ce_enter_cond(-s: String, -lim: Lp.Limit, -s2: String,
  pre: {s == Wr.put_nat(0n, LoopEntry.lp_spell_limit(lim, s2)) : String}, fl: {LoopEntry.lp_limit_fits(lim) == True{} : Bool},
  d: Wr.Dec<Lp.Cond>, cc: le.ci_cond(s2, d)) -> le.ci_ev(s, FLp.get_ev.enter.cond(lim, d)):
  match d:
    case Wr.Got{+c, +s3}:
      (e, fc) = cc
      le.ce_enter_prompt(s, lim, c, s3,
        le.into(s, y => Wr.put_nat(0n, LoopEntry.lp_spell_limit(lim, y)), s2, LoopEntry.lp_spell_cond(c, s3), pre, e),
        fl, fc, FLp.get_mstr(s3), le.ci_mstr_all(s3))
    case Wr.Bad{}:
      Unit{}

def le.ce_enter(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Lp.Limit>, ck: le.ci_limit(s1, d)) -> le.ci_ev(s, FLp.get_ev.enter(d)):
  match d:
    case Wr.Got{+lim, +s2}:
      (e, fl) = ck
      le.ce_enter_cond(s, lim, s2,
        le.into(s, y => Wr.put_nat(0n, y), s1, LoopEntry.lp_spell_limit(lim, s2), pre, e),
        fl, FLp.get_cond(s2), le.ci_cond_all(s2))
    case Wr.Bad{}:
      Unit{}

def le.ce_prompt(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<String>, ct: le.ci_str(s1, d)) -> le.ci_ev(s, FLp.get_ev.prompt(d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e, f) = ct
      (le.into(s, y => Wr.put_nat(3n, y), s1, Wr.put_str(t, s2), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def le.ce_settled_funded(-s: String, -k: Nat, -o: Lp.Out, -b: Bool, -now: Nat, -s5: String,
  pre: {s == Wr.put_nat(4n, Wr.put_nat(k, LoopEntry.lp_spell_out(o, Wr.put_bool(b, Wr.put_nat(now, s5))))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool}, fn: {LawsBase.wire_fits(now) == True{} : Bool},
  d: Wr.Dec<Bool>, cb: le.ci_bool(s5, d)) -> le.ci_ev(s, FLp.get_ev.settled.funded(k, o, b, now, d)):
  match d:
    case Wr.Got{+fu, +s6}:
      (le.into(s, y => Wr.put_nat(4n, Wr.put_nat(k, LoopEntry.lp_spell_out(o, Wr.put_bool(b, Wr.put_nat(now, y))))), s5, Wr.put_bool(fu, s6), pre, cb),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), LawsBase.wire_fits(now), fk, fn))
    case Wr.Bad{}:
      Unit{}

def le.ce_settled_now(-s: String, -k: Nat, -o: Lp.Out, -b: Bool, -s4: String,
  pre: {s == Wr.put_nat(4n, Wr.put_nat(k, LoopEntry.lp_spell_out(o, Wr.put_bool(b, s4)))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool},
  d: Wr.Dec<Nat>, cn: le.ci_nat(s4, d)) -> le.ci_ev(s, FLp.get_ev.settled.now(k, o, b, d)):
  match d:
    case Wr.Got{+now, +s5}:
      (e, fn) = cn
      le.ce_settled_funded(s, k, o, b, now, s5,
        le.into(s, y => Wr.put_nat(4n, Wr.put_nat(k, LoopEntry.lp_spell_out(o, Wr.put_bool(b, y)))), s4, Wr.put_nat(now, s5), pre, e),
        fk, fn, Wr.get_bool(s5), le.ci_bool_all(s5))
    case Wr.Bad{}:
      Unit{}

def le.ce_settled_blocked(-s: String, -k: Nat, -o: Lp.Out, -s3: String,
  pre: {s == Wr.put_nat(4n, Wr.put_nat(k, LoopEntry.lp_spell_out(o, s3))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool},
  d: Wr.Dec<Bool>, cb: le.ci_bool(s3, d)) -> le.ci_ev(s, FLp.get_ev.settled.blocked(k, o, d)):
  match d:
    case Wr.Got{+b, +s4}:
      le.ce_settled_now(s, k, o, b, s4,
        le.into(s, y => Wr.put_nat(4n, Wr.put_nat(k, LoopEntry.lp_spell_out(o, y))), s3, Wr.put_bool(b, s4), pre, cb),
        fk, Wr.get_nat(s4), le.ci_nat_all(s4))
    case Wr.Bad{}:
      Unit{}

def le.ce_settled_out(-s: String, -k: Nat, -s2: String,
  pre: {s == Wr.put_nat(4n, Wr.put_nat(k, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool},
  d: Wr.Dec<Lp.Out>, co: le.ci_out(s2, d)) -> le.ci_ev(s, FLp.get_ev.settled.out(k, d)):
  match d:
    case Wr.Got{+o, +s3}:
      le.ce_settled_blocked(s, k, o, s3,
        le.into(s, y => Wr.put_nat(4n, Wr.put_nat(k, y)), s2, LoopEntry.lp_spell_out(o, s3), pre, co),
        fk, Wr.get_bool(s3), le.ci_bool_all(s3))
    case Wr.Bad{}:
      Unit{}

def le.ce_settled(-s: String, -s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Nat>, cn: le.ci_nat(s1, d)) -> le.ci_ev(s, FLp.get_ev.settled(d)):
  match d:
    case Wr.Got{+k, +s2}:
      (e, fk) = cn
      le.ce_settled_out(s, k, s2,
        le.into(s, y => Wr.put_nat(4n, y), s1, Wr.put_nat(k, s2), pre, e),
        fk, FLp.get_out(s2), le.ci_out_all(s2))
    case Wr.Bad{}:
      Unit{}

def le.ce_judged_funded(-s: String, -k: Nat, -ev: Lp.Evid, -b: Bool, -now: Nat, -s5: String,
  pre: {s == Wr.put_nat(5n, Wr.put_nat(k, LoopEntry.lp_spell_evid(ev, Wr.put_bool(b, Wr.put_nat(now, s5))))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool}, fe: {LoopEntry.lp_evid_fits(ev) == True{} : Bool}, fn: {LawsBase.wire_fits(now) == True{} : Bool},
  d: Wr.Dec<Bool>, cb: le.ci_bool(s5, d)) -> le.ci_ev(s, FLp.get_ev.judged.funded(k, ev, b, now, d)):
  match d:
    case Wr.Got{+fu, +s6}:
      (le.into(s, y => Wr.put_nat(5n, Wr.put_nat(k, LoopEntry.lp_spell_evid(ev, Wr.put_bool(b, Wr.put_nat(now, y))))), s5, Wr.put_bool(fu, s6), pre, cb),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), Bool.and(LoopEntry.lp_evid_fits(ev), LawsBase.wire_fits(now)), fk,
          LAWireSpell.ws_and_tt(LoopEntry.lp_evid_fits(ev), LawsBase.wire_fits(now), fe, fn)))
    case Wr.Bad{}:
      Unit{}

def le.ce_judged_now(-s: String, -k: Nat, -ev: Lp.Evid, -b: Bool, -s4: String,
  pre: {s == Wr.put_nat(5n, Wr.put_nat(k, LoopEntry.lp_spell_evid(ev, Wr.put_bool(b, s4)))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool}, fe: {LoopEntry.lp_evid_fits(ev) == True{} : Bool},
  d: Wr.Dec<Nat>, cn: le.ci_nat(s4, d)) -> le.ci_ev(s, FLp.get_ev.judged.now(k, ev, b, d)):
  match d:
    case Wr.Got{+now, +s5}:
      (e, fn) = cn
      le.ce_judged_funded(s, k, ev, b, now, s5,
        le.into(s, y => Wr.put_nat(5n, Wr.put_nat(k, LoopEntry.lp_spell_evid(ev, Wr.put_bool(b, y)))), s4, Wr.put_nat(now, s5), pre, e),
        fk, fe, fn, Wr.get_bool(s5), le.ci_bool_all(s5))
    case Wr.Bad{}:
      Unit{}

def le.ce_judged_blocked(-s: String, -k: Nat, -ev: Lp.Evid, -s3: String,
  pre: {s == Wr.put_nat(5n, Wr.put_nat(k, LoopEntry.lp_spell_evid(ev, s3))) : String},
  fk: {LawsBase.wire_fits(k) == True{} : Bool}, fe: {LoopEntry.lp_evid_fits(ev) == True{} : Bool},
  d: Wr.Dec<Bool>, cb: le.ci_bool(s3, d)) -> le.ci_ev(s, FLp.get_ev.judged.blocked(k, ev, d)):
  match d:
    case Wr.Got{+b, +s4}:
      le.ce_judged_now(s, k, ev, b, s4,
        le.into(s, y => Wr.put_nat(5n, Wr.put_nat(k, LoopEntry.lp_spell_evid(ev, y))), s3, Wr.put_bool(b, s4), pre, cb),
        fk, fe, Wr.get_nat(s4), le.ci_nat_all(s4))
    case Wr.Bad{}:
      Unit{}

def le.ce_judged_ev(-s: String, -k: Nat, -s2: String,
  pre: {s == Wr.put_nat(5n, Wr.put_nat(k, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool},
  d: Wr.Dec<Lp.Evid>, cv: le.ci_evid(s2, d)) -> le.ci_ev(s, FLp.get_ev.judged.ev(k, d)):
  match d:
    case Wr.Got{+ev, +s3}:
      (e, fe) = cv
      le.ce_judged_blocked(s, k, ev, s3,
        le.into(s, y => Wr.put_nat(5n, Wr.put_nat(k, y)), s2, LoopEntry.lp_spell_evid(ev, s3), pre, e),
        fk, fe, Wr.get_bool(s3), le.ci_bool_all(s3))
    case Wr.Bad{}:
      Unit{}

def le.ce_judged(-s: String, -s1: String, pre: {s == Wr.put_nat(5n, s1) : String}, d: Wr.Dec<Nat>, cn: le.ci_nat(s1, d)) -> le.ci_ev(s, FLp.get_ev.judged(d)):
  match d:
    case Wr.Got{+k, +s2}:
      (e, fk) = cn
      le.ce_judged_ev(s, k, s2,
        le.into(s, y => Wr.put_nat(5n, y), s1, Wr.put_nat(k, s2), pre, e),
        fk, FLp.get_evid(s2), le.ci_evid_all(s2))
    case Wr.Bad{}:
      Unit{}

def le.ce_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> le.ci_ev(s, FLp.get_ev.tag(t, s1)):
  match t:
    case 0n:
      le.ce_enter(s, s1, e, FLp.get_limit(s1), le.ci_limit_all(s1))
    case 1n:
      (e, {==})
    case 2n:
      (e, {==})
    case 3n:
      le.ce_prompt(s, s1, e, Wr.get_str(s1), le.ci_str_all(s1))
    case 4n:
      le.ce_settled(s, s1, e, Wr.get_nat(s1), le.ci_nat_all(s1))
    case 5n:
      le.ce_judged(s, s1, e, Wr.get_nat(s1), le.ci_nat_all(s1))
    case 6n:
      (e, {==})
    case 7n+x:
      Unit{}

def le.ce_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_ev(s, FLp.get_ev.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.ce_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

# every event the reader reads is spelled, and fits
def le.ci_ev_all(+s: String) -> le.ci_ev(s, FLp.get_ev(s)):
  le.ce_go(s, Wr.get_nat(s), le.ci_nat_all(s))

# ---- the request ----

def le.ci_req(s: String, d: Wr.Dec<FLp.Req>) -> Type:
  match d:
    case Wr.Got{+r, rest}:
      {s == LoopEntry.lp_spell_req(r, rest) : String} & {LoopEntry.lp_req_fits(r) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def le.cr_ev(-s0: String, -x: Lp.St, -s1: String, pre: {s0 == Wr.put_nat(0n, LoopEntry.lp_spell_st(x, s1)) : String}, fx: {LoopEntry.lp_st_fits(x) == True{} : Bool},
  d: Wr.Dec<Lp.Ev>, ce: le.ci_ev(s1, d)) -> le.ci_req(s0, FLp.get_req.ev(x, d)):
  match d:
    case Wr.Got{+e, +s2}:
      (e1, f) = ce
      (le.into(s0, y => Wr.put_nat(0n, LoopEntry.lp_spell_st(x, y)), s1, LoopEntry.lp_spell_ev(e, s2), pre, e1),
        LAWireSpell.ws_and_tt(LoopEntry.lp_st_fits(x), LoopEntry.lp_ev_fits(e), fx, f))
    case Wr.Bad{}:
      Unit{}

def le.cr_st(-s0: String, -s1: String, pre: {s0 == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Lp.St>, cs: le.ci_st(s1, d)) -> le.ci_req(s0, FLp.get_req.st(d)):
  match d:
    case Wr.Got{+x, +s2}:
      (e, f) = cs
      le.cr_ev(s0, x, s2,
        le.into(s0, y => Wr.put_nat(0n, y), s1, LoopEntry.lp_spell_st(x, s2), pre, e),
        f, FLp.get_ev(s2), le.ci_ev_all(s2))
    case Wr.Bad{}:
      Unit{}

def le.cr_evid(-s0: String, -u: Bool, -s1: String, pre: {s0 == Wr.put_nat(1n, Wr.put_bool(u, s1)) : String},
  d: Wr.Dec<Lp.Evid>, cv: le.ci_evid(s1, d)) -> le.ci_req(s0, FLp.get_req.evid(u, d)):
  match d:
    case Wr.Got{+ev, +s2}:
      (e, f) = cv
      (le.into(s0, y => Wr.put_nat(1n, Wr.put_bool(u, y)), s1, LoopEntry.lp_spell_evid(ev, s2), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def le.cr_until(-s0: String, -s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, cb: le.ci_bool(s1, d)) -> le.ci_req(s0, FLp.get_req.until(d)):
  match d:
    case Wr.Got{+u, +s2}:
      le.cr_evid(s0, u, s2,
        le.into(s0, y => Wr.put_nat(1n, y), s1, Wr.put_bool(u, s2), pre, cb),
        FLp.get_evid(s2), le.ci_evid_all(s2))
    case Wr.Bad{}:
      Unit{}

def le.cr_tag(-s0: String, t: Nat, +s1: String, e: {s0 == Wr.put_nat(t, s1) : String}) -> le.ci_req(s0, FLp.get_req.tag(t, s1)):
  match t:
    case 0n:
      le.cr_st(s0, s1, e, FLp.get_st(s1), le.ci_st_all(s1))
    case 1n:
      le.cr_until(s0, s1, e, Wr.get_bool(s1), le.ci_bool_all(s1))
    case 2n+x:
      Unit{}

def le.cr_go(-s: String, d: Wr.Dec<Nat>, cn: le.ci_nat(s, d)) -> le.ci_req(s, FLp.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = cn
      le.cr_tag(s, t, s1, e)
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, and fits
def le.ci_req_all(+s: String) -> le.ci_req(s, FLp.get_req(s)):
  le.cr_go(s, Wr.get_nat(s), le.ci_nat_all(s))
