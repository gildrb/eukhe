# eukhe: the proof of LAW dmw_ffi_reads_only_requests
#
# PROOF: whatever a decoder of the entry reads is the spelling of what it
# read, then its rest, and fits the wire (dmc.*, tag by tag with the
# wire's exactness laws: an unknown tag is Bad; a fact with
# wire_bool_exact); the stages carry the input spelled up to their field
# (`pre`), so an answer that is no error comes from a request read whole,
# nothing left, and is the spelled resolution (dmro.fin with LS.dms.res).

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LS

# s spelled up to a field a is s spelled up to its spelling b
def dmc.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Decoders: what each read is its spelling, then its rest, and fits
# -----------------------------------------------------------------

def dmc.Saved(s: String, d: Wr.Dec<Dm.Saved>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == DefaultModel.dmw_spell_saved(x, r) : String} & {DefaultModel.dmw_saved_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dmc.saved.m(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> dmc.Saved(s, FDm.get_saved.m(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +ee = ed
      (dmc.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, ee)), Wire.wire_nat_decoded_fits(s0, x, s1, ee))
    case Wr.Bad{}:
      Unit{}

def dmc.saved.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dmc.Saved(s, FDm.get_saved.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          dmc.saved.m(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dmc.saved(+s: String) -> dmc.Saved(s, FDm.get_saved(s)):
  dmc.saved.go(s, Wr.get_nat(s), {==})

def dmc.Next(s: String, d: Wr.Dec<Dm.Next>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == DefaultModel.dmw_spell_next(x, r) : String} & {DefaultModel.dmw_next_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dmc.next.n(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> dmc.Next(s, FDm.get_next.n(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +ee = ed
      (dmc.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, ee)), Wire.wire_nat_decoded_fits(s0, x, s1, ee))
    case Wr.Bad{}:
      Unit{}

def dmc.next.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dmc.Next(s, FDm.get_next.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          dmc.next.n(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dmc.next(+s: String) -> dmc.Next(s, FDm.get_next(s)):
  dmc.next.go(s, Wr.get_nat(s), {==})

# the request: its spelling, then its rest, and it fits
def dmc.In(s: String, d: Wr.Dec<Dm.In>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == DefaultModel.dmw_spell_req(x, r) : String} & {DefaultModel.dmw_in_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dmc.in.next(+s: String, +saved: Dm.Saved, +cat: Bool, +key: Bool, +out: Bool, +s4: String, pre: {s == DefaultModel.dmw_spell_saved(saved, Wr.put_bool(cat, Wr.put_bool(key, Wr.put_bool(out, s4)))) : String}, fs: {DefaultModel.dmw_saved_fits(saved) == True{} : Bool}, d: Wr.Dec<Dm.Next>, xd: dmc.Next(s4, d)) -> dmc.In(s, FDm.get_in.next(saved, cat, key, out, d)):
  match d:
    case Wr.Got{+next, +s5}:
      (e, fn) = xd
      (dmc.step(z => DefaultModel.dmw_spell_saved(saved, Wr.put_bool(cat, Wr.put_bool(key, Wr.put_bool(out, z)))), s, s4, DefaultModel.dmw_spell_next(next, s5), pre, e), LAWireSpell.ws_and_tt(DefaultModel.dmw_saved_fits(saved), DefaultModel.dmw_next_fits(next), fs, fn))
    case Wr.Bad{}:
      Unit{}

def dmc.in.out(+s: String, +saved: Dm.Saved, +cat: Bool, +key: Bool, +s3: String, pre: {s == DefaultModel.dmw_spell_saved(saved, Wr.put_bool(cat, Wr.put_bool(key, s3))) : String}, fs: {DefaultModel.dmw_saved_fits(saved) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == d : Wr.Dec<Bool>}) -> dmc.In(s, FDm.get_in.out(saved, cat, key, d)):
  match d:
    case Wr.Got{+out, +s4}:
      dmc.in.next(s, saved, cat, key, out, s4, dmc.step(z => DefaultModel.dmw_spell_saved(saved, Wr.put_bool(cat, Wr.put_bool(key, z))), s, s3, Wr.put_bool(out, s4), pre, Wire.wire_bool_exact(s3, out, s4, ed)), fs, FDm.get_next(s4), dmc.next(s4))
    case Wr.Bad{}:
      Unit{}

def dmc.in.key(+s: String, +saved: Dm.Saved, +cat: Bool, +s2: String, pre: {s == DefaultModel.dmw_spell_saved(saved, Wr.put_bool(cat, s2)) : String}, fs: {DefaultModel.dmw_saved_fits(saved) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> dmc.In(s, FDm.get_in.key(saved, cat, d)):
  match d:
    case Wr.Got{+key, +s3}:
      dmc.in.out(s, saved, cat, key, s3, dmc.step(z => DefaultModel.dmw_spell_saved(saved, Wr.put_bool(cat, z)), s, s2, Wr.put_bool(key, s3), pre, Wire.wire_bool_exact(s2, key, s3, ed)), fs, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def dmc.in.cat(+s: String, +saved: Dm.Saved, +s1: String, pre: {s == DefaultModel.dmw_spell_saved(saved, s1) : String}, fs: {DefaultModel.dmw_saved_fits(saved) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> dmc.In(s, FDm.get_in.cat(saved, d)):
  match d:
    case Wr.Got{+cat, +s2}:
      dmc.in.key(s, saved, cat, s2, dmc.step(z => DefaultModel.dmw_spell_saved(saved, z), s, s1, Wr.put_bool(cat, s2), pre, Wire.wire_bool_exact(s1, cat, s2, ed)), fs, Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dmc.in.go(+s: String, d: Wr.Dec<Dm.Saved>, xd: dmc.Saved(s, d)) -> dmc.In(s, FDm.get_in.go(d)):
  match d:
    case Wr.Got{+saved, +s1}:
      (e, fs) = xd
      dmc.in.cat(s, saved, s1, e, fs, Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def dmc.in(+s: String) -> dmc.In(s, FDm.get_in(s)):
  dmc.in.go(s, FDm.get_saved(s), dmc.saved(s))

# The entry
# ---------

def dmro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, Dm.In, x => {(s, (DefaultModel.dmw_in_fits(x), a)) == (DefaultModel.dmw_spell_req(x, ""), (True{}, DefaultModel.dmw_spell_answer(x))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def dmro.top_eq(+s: String, +x: Dm.In, +a: String, e: {s == DefaultModel.dmw_spell_req(x, "") : String}, f: {DefaultModel.dmw_in_fits(x) == True{} : Bool}, ea: {a == DefaultModel.dmw_spell_answer(x) : String}) -> {(s, (DefaultModel.dmw_in_fits(x), a)) == (DefaultModel.dmw_spell_req(x, ""), (True{}, DefaultModel.dmw_spell_answer(x))) : String & (Bool & String)}:
  %Equal.sym(String, s, DefaultModel.dmw_spell_req(x, ""), e) : {(_, (DefaultModel.dmw_in_fits(x), a)) == (DefaultModel.dmw_spell_req(x, ""), (True{}, DefaultModel.dmw_spell_answer(x))) : String & (Bool & String)}
  %Equal.sym(Bool, DefaultModel.dmw_in_fits(x), True{}, f) : {(DefaultModel.dmw_spell_req(x, ""), (_, a)) == (DefaultModel.dmw_spell_req(x, ""), (True{}, DefaultModel.dmw_spell_answer(x))) : String & (Bool & String)}
  %Equal.sym(String, a, DefaultModel.dmw_spell_answer(x), ea) : {(DefaultModel.dmw_spell_req(x, ""), (True{}, _)) == (DefaultModel.dmw_spell_req(x, ""), (True{}, DefaultModel.dmw_spell_answer(x))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def dmro.fin(+s: String, +x: Dm.In, r: String, pre: {s == DefaultModel.dmw_spell_req(x, r) : String}, f: {DefaultModel.dmw_in_fits(x) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FDm.ffi.end(Wr.end(r), x)) == False{} : Bool}) -> dmro.G(s, FDm.ffi.end(Wr.end(r), x)):
  match r:
    case SNil{}:
      (x, dmro.top_eq(s, x, FDm.ffi.end(True{}, x), pre, f, LS.dms.res(Dm.resolve(x), "")))
    case SCon{c, y}:
      LAWireSpell.ws_absurd(dmro.G(s, FDm.ffi.end(False{}, x)), ok)

def dmro.main(+s: String, d: Wr.Dec<Dm.In>, inv: dmc.In(s, d), ok: {LawsBase.wire_opens_err(FDm.ffi.go(d)) == False{} : Bool}) -> dmro.G(s, FDm.ffi.go(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = inv
      dmro.fin(s, x, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(dmro.G(s, Wr.err("default_model: malformed request")), ok)

def DefaultModel.dmw_ffi_reads_only_requests(s, ok):
  dmro.main(s, FDm.get_in(s), dmc.in(s), ok)
