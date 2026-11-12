# eukhe: the proof of LAW wait_entry_open_reads_only
# Whatever the stepper's open decoder reads is a spelled tag and, for
# Some, a spelled Nat that fits, then its rest (wire_nat_exact,
# wire_nat_decoded_fits). Nothing read, or a rest that is not empty, opens
# the refused state with the malformed-open error, which the premise
# excludes; a deadline read whole is the input's spelling.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# a deadline, then rest, spelled
def od.sp(dl: Maybe<&2, Nat>, rest: String) -> String:
  match dl:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{d}:
      Wr.put_nat(1n, Wr.put_nat(d, rest))

def od.Dl(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{dl, rest}:
      {s == od.sp(dl, rest) : String} & {LawsBase.wire_mfits(dl) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def od.some(-s: String, -s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, inv: LA.wr.Nat(s0, d)) -> od.Dl(s, FWt.get_dl.some(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e1, f1) = inv
      (LA.wr.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(n, s1), pre, e1), f1)
    case Wr.Bad{}:
      Unit{}

def od.tag(-s: String, t: Nat, +s0: String, pre: {s == Wr.put_nat(t, s0) : String}) -> od.Dl(s, FWt.get_dl.tag(t, s0)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      od.some(s, s0, pre, Wr.get_nat(s0), LA.wr.nat(s0))
    case 2n+p:
      Unit{}

def od.go(-s: String, d: Wr.Dec<Nat>, inv: LA.wr.Nat(s, d)) -> od.Dl(s, FWt.get_dl.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      (e, f) = inv
      od.tag(s, t, s0, e)
    case Wr.Bad{}:
      Unit{}

def od.G(s: String) -> Type:
  Sigma<&1, &1, Maybe<&2, Nat>, dl => {(s, LawsBase.wire_mfits(dl)) == (WaitLaws.ww_spell_dl(dl), True{}) : String & Bool}>

def od.pair(-s: String, -x: String, -b: Bool, e: {s == x : String}, f: {b == True{} : Bool}) -> {(s, b) == (x, True{}) : String & Bool}:
  %Equal.sym(String, s, x, e) : {(_, b) == (x, True{}) : String & Bool}
  %Equal.sym(Bool, b, True{}, f) : {(x, _) == (x, True{}) : String & Bool}
  {==}

# a deadline read whole is the input's spelling
def od.done(-s: String, dl: Maybe<&2, Nat>, pre: {s == od.sp(dl, "") : String}, f: {LawsBase.wire_mfits(dl) == True{} : Bool}) -> od.G(s):
  match dl:
    case None{}:
      (None{}, od.pair(s, WaitLaws.ww_spell_dl(None{}), LawsBase.wire_mfits(None{}), pre, f))
    case Some{+d}:
      (Some{d}, od.pair(s, WaitLaws.ww_spell_dl(Some{d}), LawsBase.wire_mfits(Some{d}), pre, f))

# a deadline read with input left over opens the refused state
def od.fin(-s: String, +dl: Maybe<&2, Nat>, rest: String, pre: {s == od.sp(dl, rest) : String}, f: {LawsBase.wire_mfits(dl) == True{} : Bool}, ok: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.open.end(Wr.end(rest), dl))) == False{} : Bool}) -> od.G(s):
  match rest:
    case SNil{}:
      od.done(s, dl, pre, f)
    case SCon{h, t}:
      LA.pw.absurd(od.G(s), ok)

def od.main(-s: String, d: Wr.Dec<Maybe<&2, Nat>>, inv: od.Dl(s, d), ok: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.open.dl(d))) == False{} : Bool}) -> od.G(s):
  match d:
    case Wr.Got{+dl, +rest}:
      (e, f) = inv
      od.fin(s, dl, rest, e, f, ok)
    case Wr.Bad{}:
      LA.pw.absurd(od.G(s), ok)

def WaitLaws.wait_entry_open_reads_only(s, other):
  od.main(s, FWt.get_dl(s), od.go(s, Wr.get_nat(s), LA.wr.nat(s)), other)
