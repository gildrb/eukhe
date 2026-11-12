# eukhe: the proof of LAW tool_call_entry_reads_only_events
# What the entry's event decoder reads is the spelling of an event, then
# its rest (tre.go: the tag by wire_nat_exact, each Bool by
# wire_bool_exact, a tag of 2 or more reads nothing); the reply is the
# error form unless nothing is left, and then the input is the event's
# spelling.

import Base
import ../../bend/tool_call.bend as Tc
import ../../bend/ffi_tool_call.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/tool_call.bend as ToolCall
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./base.bend as LA

# an event as the Harness writes it, then rest
def tre.sp(e: Tc.Ev, rest: String) -> String:
  match e:
    case Tc.Report{}:
      Wr.put_nat(0n, rest)
    case Tc.End{t, a}:
      Wr.put_nat(1n, Wr.put_bool(t, Wr.put_bool(a, rest)))

def tre.sp_nil(e: Tc.Ev) -> {tre.sp(e, "") == ToolCall.tc_spell(e) : String}:
  match e:
    case Tc.Report{}:
      {==}
    case Tc.End{t, a}:
      {==}

# what the decoder reads is its spelling, then its rest
def tre.Inv(i: String, d: Wr.Dec<Tc.Ev>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {i == tre.sp(e, r) : String}
    case Wr.Bad{}:
      Unit

def tre.aborted(+i: String, +t: Bool, +s2: String, pre: {i == Wr.put_nat(1n, Wr.put_bool(t, s2)) : String}, r: Wr.Dec<Bool>, er: {Wr.get_bool(s2) == r : Wr.Dec<Bool>}) -> tre.Inv(i, FTc.get_ev.aborted(t, r)):
  match r:
    case Wr.Got{+a, +s3}:
      LA.tp.step(z => Wr.put_nat(1n, Wr.put_bool(t, z)), i, s2, Wr.put_bool(a, s3), pre, Wire.wire_bool_exact(s2, a, s3, er))
    case Wr.Bad{}:
      Unit{}

def tre.threw(+i: String, +s1: String, pre: {i == Wr.put_nat(1n, s1) : String}, r: Wr.Dec<Bool>, er: {Wr.get_bool(s1) == r : Wr.Dec<Bool>}) -> tre.Inv(i, FTc.get_ev.threw(r)):
  match r:
    case Wr.Got{+t, +s2}:
      tre.aborted(i, t, s2, LA.tp.step(z => Wr.put_nat(1n, z), i, s1, Wr.put_bool(t, s2), pre, Wire.wire_bool_exact(s1, t, s2, er)), Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def tre.tag(+i: String, n: Nat, +s1: String, pre: {i == Wr.put_nat(n, s1) : String}) -> tre.Inv(i, FTc.get_ev.tag(n, s1)):
  match n:
    case 0n:
      pre
    case 1n:
      tre.threw(i, s1, pre, Wr.get_bool(s1), {==})
    case 2n+p:
      Unit{}

def tre.go(+i: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(i) == r : Wr.Dec<Nat>}) -> tre.Inv(i, FTc.get_ev.go(r)):
  match r:
    case Wr.Got{+n, +s1}:
      tre.tag(i, n, s1, Wire.wire_nat_exact(i, n, s1, er))
    case Wr.Bad{}:
      Unit{}

def tre.G(i: String) -> Type:
  Sigma<&1, &1, Tc.Ev, e => {i == ToolCall.tc_spell(e) : String}>

# the end check: nothing left, the input is the event's spelling; anything
# left is the error form
def tre.fin(+i: String, +c: Tc.C, +e: Tc.Ev, r: String, pre: {i == tre.sp(e, r) : String}, ok: {String.eq(ToolCall.tc_reply(FTc.step.end(Wr.end(r), c, e)), ToolCall.tc_bad_event()) == False{} : Bool}) -> tre.G(i):
  match r:
    case SNil{}:
      (e, Equal.trans(String, i, tre.sp(e, ""), ToolCall.tc_spell(e), pre, tre.sp_nil(e)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(tre.G(i), ok)

def tre.main(+i: String, +c: Tc.C, d: Wr.Dec<Tc.Ev>, inv: tre.Inv(i, d), ok: {String.eq(ToolCall.tc_reply(FTc.step.ev(c, d)), ToolCall.tc_bad_event()) == False{} : Bool}) -> tre.G(i):
  match d:
    case Wr.Got{+e, +r}:
      tre.fin(i, c, e, r, inv, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tre.G(i), ok)

def ToolCall.tool_call_entry_reads_only_events(c, i, other):
  tre.main(i, c, FTc.get_ev(i), tre.go(i, Wr.get_nat(i), {==}), other)
