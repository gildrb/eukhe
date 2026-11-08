# eukhe: the proof of LAW orphan_ffi_reads_only_requests
#
# PROOF: whatever a decoder of the entry reads is the spelling of what it
# read, then its rest, and fits the wire (oc.*, tag by tag with the wire's
# exactness laws: an unknown tag is Bad); the entry's stages carry the
# input spelled up to their field (or.*: `pre`), so an answer that is no
# error comes from a request read whole, nothing left, and is the spelled
# spec decision (or.fin with LA.oe.answer).

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/orphan.bend as Or
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA

# s spelled up to a field a is s spelled up to its spelling b
def oc.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Decoders: what each read is its spelling, then its rest, and fits
# -----------------------------------------------------------------

def oc.Win(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Orphan.orphan_spell_mwindow(m, r) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def oc.Work(s: String, d: Wr.Dec<Or.Work>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == Orphan.orphan_spell_work(k, r) : String}
    case Wr.Bad{}:
      Unit

def oc.win.some(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> oc.Win(s, FO.get_window.some(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +ee = ed
      (oc.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, ee)), Wire.wire_nat_decoded_fits(s0, x, s1, ee))
    case Wr.Bad{}:
      Unit{}

def oc.win.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> oc.Win(s, FO.get_window.of(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          oc.win.some(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def oc.win(+s: String) -> oc.Win(s, FO.get_window(s)):
  oc.win.go(s, Wr.get_nat(s), {==})

def oc.work.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> oc.Work(s, FO.get_work.of(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def oc.work(+s: String) -> oc.Work(s, FO.get_work(s)):
  oc.work.go(s, Wr.get_nat(s), {==})

# the request: its spelling, then its rest, and it fits
def oc.Req(s: String, d: Wr.Dec<FO.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Orphan.orphan_spell_req(q, r) : String} & {Orphan.orphan_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def oc.req.work(+s: String, +m: Maybe<&2, Nat>, +a: Nat, +s2: String, pre: {s == Orphan.orphan_spell_mwindow(m, Wr.put_nat(a, s2)) : String}, fm: {LawsBase.wire_mfits(m) == True{} : Bool}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, d: Wr.Dec<Or.Work>, xd: oc.Work(s2, d)) -> oc.Req(s, FO.get_req.work(m, a, d)):
  match d:
    case Wr.Got{+k, +s3}:
      (oc.step(z => Orphan.orphan_spell_mwindow(m, Wr.put_nat(a, z)), s, s2, Orphan.orphan_spell_work(k, s3), pre, xd), LAWireSpell.ws_and_tt(LawsBase.wire_mfits(m), LawsBase.wire_fits(a), fm, fa))
    case Wr.Bad{}:
      Unit{}

def oc.req.absent(+s: String, +m: Maybe<&2, Nat>, +s1: String, pre: {s == Orphan.orphan_spell_mwindow(m, s1) : String}, fm: {LawsBase.wire_mfits(m) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> oc.Req(s, FO.get_req.absent(m, d)):
  match d:
    case Wr.Got{+a, +s2}:
      +ee = ed
      oc.req.work(s, m, a, s2, oc.step(z => Orphan.orphan_spell_mwindow(m, z), s, s1, Wr.put_nat(a, s2), pre, Wire.wire_nat_exact(s1, a, s2, ee)), fm, Wire.wire_nat_decoded_fits(s1, a, s2, ee), FO.get_work(s2), oc.work(s2))
    case Wr.Bad{}:
      Unit{}

def oc.req.window(+s: String, d: Wr.Dec<Maybe<&2, Nat>>, xd: oc.Win(s, d)) -> oc.Req(s, FO.get_req.window(d)):
  match d:
    case Wr.Got{+m, +s1}:
      (e1, fm) = xd
      oc.req.absent(s, m, s1, e1, fm, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def oc.req(+s: String) -> oc.Req(s, FO.get_req(s)):
  oc.req.window(s, FO.get_window(s), oc.win(s))

# The entry
# ---------

def ro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FO.Req, q => {(s, (Orphan.orphan_req_fits(q), a)) == (Orphan.orphan_spell_req(q, ""), (True{}, Orphan.orphan_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def ro.top_eq(+s: String, +q: FO.Req, +a: String, e: {s == Orphan.orphan_spell_req(q, "") : String}, f: {Orphan.orphan_req_fits(q) == True{} : Bool}, ea: {a == Orphan.orphan_spell_answer(q) : String}) -> {(s, (Orphan.orphan_req_fits(q), a)) == (Orphan.orphan_spell_req(q, ""), (True{}, Orphan.orphan_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, Orphan.orphan_spell_req(q, ""), e) : {(_, (Orphan.orphan_req_fits(q), a)) == (Orphan.orphan_spell_req(q, ""), (True{}, Orphan.orphan_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, Orphan.orphan_req_fits(q), True{}, f) : {(Orphan.orphan_spell_req(q, ""), (_, a)) == (Orphan.orphan_spell_req(q, ""), (True{}, Orphan.orphan_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, Orphan.orphan_spell_answer(q), ea) : {(Orphan.orphan_spell_req(q, ""), (True{}, _)) == (Orphan.orphan_spell_req(q, ""), (True{}, Orphan.orphan_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def ro.fin(+s: String, +q: FO.Req, r: String, pre: {s == Orphan.orphan_spell_req(q, r) : String}, f: {Orphan.orphan_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FO.ffi.fin(Wr.end(r), q)) == False{} : Bool}) -> ro.G(s, FO.ffi.fin(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, ro.top_eq(s, q, FO.ffi.fin(True{}, q), pre, f, LA.oe.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(ro.G(s, FO.ffi.fin(False{}, q)), ok)

def ro.main(+s: String, d: Wr.Dec<FO.Req>, inv: oc.Req(s, d), ok: {LawsBase.wire_opens_err(FO.ffi.go(d)) == False{} : Bool}) -> ro.G(s, FO.ffi.go(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      ro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("orphan: malformed request")), ok)

def Orphan.orphan_ffi_reads_only_requests(s, ok):
  ro.main(s, FO.get_req(s), oc.req(s), ok)
