# eukhe: the proof of LAW tool_call_gate_reads_only_questions
# What the entry's gate decoder reads is the spelling of a question, then
# its rest (tgq.go: every tag by wire_nat_exact, every Bool by
# wire_bool_exact, a replay policy and a tool as their spellings, an
# unknown tag reads nothing); the answer is the error form unless nothing
# is left, and then the input is the question's spelling.

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

# a question as the Harness writes it, then rest
def tgq.sp(q: Tc.Gate, rest: String) -> String:
  match q:
    case Tc.Enter{f, t}:
      Wr.put_nat(0n, Wr.put_bool(f, ToolCall.tc_spell_now(t, rest)))
    case Tc.Recover{f, p, t}:
      Wr.put_nat(1n, Wr.put_bool(f, ToolCall.tc_spell_replay(p, ToolCall.tc_spell_now(t, rest))))
    case Tc.Stop{f, x, i}:
      Wr.put_nat(2n, Wr.put_bool(f, Wr.put_bool(x, Wr.put_bool(i, rest))))

def tgq.sp_nil(q: Tc.Gate) -> {tgq.sp(q, "") == ToolCall.tc_spell_gate(q) : String}:
  match q:
    case Tc.Enter{f, t}:
      {==}
    case Tc.Recover{f, p, t}:
      {==}
    case Tc.Stop{f, x, i}:
      {==}

# A replay policy
# ---------------

def tgq.RP(s: String, d: Wr.Dec<Tc.Replay>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == ToolCall.tc_spell_replay(p, r) : String}
    case Wr.Bad{}:
      Unit

def tgq.rp_tag(-s: String, n: Nat, -s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> tgq.RP(s, FTc.get_replay.tag(n, s1)):
  match n:
    case 0n:
      pre
    case 1n:
      pre
    case 2n+k:
      Unit{}

def tgq.rp_go(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> tgq.RP(s, FTc.get_replay.go(r)):
  match r:
    case Wr.Got{+n, +s1}:
      tgq.rp_tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, er))
    case Wr.Bad{}:
      Unit{}

def tgq.rp(+s: String) -> tgq.RP(s, FTc.get_replay(s)):
  tgq.rp_go(s, Wr.get_nat(s), {==})

# The tool as resolved now
# ------------------------

def tgq.NW(s: String, d: Wr.Dec<Tc.Now>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == ToolCall.tc_spell_now(t, r) : String}
    case Wr.Bad{}:
      Unit

def tgq.nw_off(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Tc.Replay>, inv: tgq.RP(s1, d)) -> tgq.NW(s, FTc.get_now.offered(d)):
  match d:
    case Wr.Got{p, r}:
      LA.tp.step(z => Wr.put_nat(1n, z), s, s1, ToolCall.tc_spell_replay(p, r), pre, inv)
    case Wr.Bad{}:
      Unit{}

def tgq.nw_tag(-s: String, n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> tgq.NW(s, FTc.get_now.tag(n, s1)):
  match n:
    case 0n:
      pre
    case 1n:
      tgq.nw_off(s, s1, pre, FTc.get_replay(s1), tgq.rp(s1))
    case 2n+k:
      Unit{}

def tgq.nw_go(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> tgq.NW(s, FTc.get_now.go(r)):
  match r:
    case Wr.Got{+n, +s1}:
      tgq.nw_tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, er))
    case Wr.Bad{}:
      Unit{}

def tgq.nw(+s: String) -> tgq.NW(s, FTc.get_now(s)):
  tgq.nw_go(s, Wr.get_nat(s), {==})

# The question
# ------------

def tgq.Q(i: String, d: Wr.Dec<Tc.Gate>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {i == tgq.sp(q, r) : String}
    case Wr.Bad{}:
      Unit

def tgq.enter(-i: String, -f: Bool, -s2: String, pre: {i == Wr.put_nat(0n, Wr.put_bool(f, s2)) : String}, d: Wr.Dec<Tc.Now>, inv: tgq.NW(s2, d)) -> tgq.Q(i, FTc.get_gate.enter(f, d)):
  match d:
    case Wr.Got{t, r}:
      LA.tp.step(z => Wr.put_nat(0n, Wr.put_bool(f, z)), i, s2, ToolCall.tc_spell_now(t, r), pre, inv)
    case Wr.Bad{}:
      Unit{}

def tgq.recover(-i: String, -f: Bool, -p: Tc.Replay, -s3: String, pre: {i == Wr.put_nat(1n, Wr.put_bool(f, ToolCall.tc_spell_replay(p, s3))) : String}, d: Wr.Dec<Tc.Now>, inv: tgq.NW(s3, d)) -> tgq.Q(i, FTc.get_gate.recover(f, p, d)):
  match d:
    case Wr.Got{t, r}:
      LA.tp.step(z => Wr.put_nat(1n, Wr.put_bool(f, ToolCall.tc_spell_replay(p, z))), i, s3, ToolCall.tc_spell_now(t, r), pre, inv)
    case Wr.Bad{}:
      Unit{}

def tgq.stored(-i: String, +f: Bool, -s2: String, pre: {i == Wr.put_nat(1n, Wr.put_bool(f, s2)) : String}, d: Wr.Dec<Tc.Replay>, inv: tgq.RP(s2, d)) -> tgq.Q(i, FTc.get_gate.stored(f, d)):
  match d:
    case Wr.Got{+p, +s3}:
      tgq.recover(i, f, p, s3, LA.tp.step(z => Wr.put_nat(1n, Wr.put_bool(f, z)), i, s2, ToolCall.tc_spell_replay(p, s3), pre, inv), FTc.get_now(s3), tgq.nw(s3))
    case Wr.Bad{}:
      Unit{}

def tgq.intent(-i: String, -f: Bool, -x: Bool, +s3: String, pre: {i == Wr.put_nat(2n, Wr.put_bool(f, Wr.put_bool(x, s3))) : String}, d: Wr.Dec<Bool>, er: {Wr.get_bool(s3) == d : Wr.Dec<Bool>}) -> tgq.Q(i, FTc.get_gate.intent(f, x, d)):
  match d:
    case Wr.Got{+j, +s4}:
      LA.tp.step(z => Wr.put_nat(2n, Wr.put_bool(f, Wr.put_bool(x, z))), i, s3, Wr.put_bool(j, s4), pre, Wire.wire_bool_exact(s3, j, s4, er))
    case Wr.Bad{}:
      Unit{}

def tgq.restart(-i: String, -f: Bool, +s2: String, pre: {i == Wr.put_nat(2n, Wr.put_bool(f, s2)) : String}, d: Wr.Dec<Bool>, er: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> tgq.Q(i, FTc.get_gate.restart(f, d)):
  match d:
    case Wr.Got{+x, +s3}:
      tgq.intent(i, f, x, s3, LA.tp.step(z => Wr.put_nat(2n, Wr.put_bool(f, z)), i, s2, Wr.put_bool(x, s3), pre, Wire.wire_bool_exact(s2, x, s3, er)), Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def tgq.found(-i: String, n: Nat, +s1: String, pre: {i == Wr.put_nat(n, s1) : String}, d: Wr.Dec<Bool>, er: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> tgq.Q(i, FTc.get_gate.found(n, d)):
  match n:
    case 0n:
      match d:
        case Wr.Got{+f, +s2}:
          tgq.enter(i, f, s2, LA.tp.step(z => Wr.put_nat(0n, z), i, s1, Wr.put_bool(f, s2), pre, Wire.wire_bool_exact(s1, f, s2, er)), FTc.get_now(s2), tgq.nw(s2))
        case Wr.Bad{}:
          Unit{}
    case 1n:
      match d:
        case Wr.Got{+f, +s2}:
          tgq.stored(i, f, s2, LA.tp.step(z => Wr.put_nat(1n, z), i, s1, Wr.put_bool(f, s2), pre, Wire.wire_bool_exact(s1, f, s2, er)), FTc.get_replay(s2), tgq.rp(s2))
        case Wr.Bad{}:
          Unit{}
    case 2n:
      match d:
        case Wr.Got{+f, +s2}:
          tgq.restart(i, f, s2, LA.tp.step(z => Wr.put_nat(2n, z), i, s1, Wr.put_bool(f, s2), pre, Wire.wire_bool_exact(s1, f, s2, er)), Wr.get_bool(s2), {==})
        case Wr.Bad{}:
          Unit{}
    case 3n+k:
      Unit{}

def tgq.go(+i: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(i) == r : Wr.Dec<Nat>}) -> tgq.Q(i, FTc.get_gate.go(r)):
  match r:
    case Wr.Got{+n, +s1}:
      tgq.found(i, n, s1, Wire.wire_nat_exact(i, n, s1, er), Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

# The answer
# ----------

def tgq.G(i: String) -> Type:
  Sigma<&1, &1, Tc.Gate, q => {i == ToolCall.tc_spell_gate(q) : String}>

def tgq.fin(-i: String, +q: Tc.Gate, r: String, pre: {i == tgq.sp(q, r) : String}, ok: {String.eq(FTc.ffi.end(Wr.end(r), q), ToolCall.tc_bad_gate()) == False{} : Bool}) -> tgq.G(i):
  match r:
    case SNil{}:
      (q, Equal.trans(String, i, tgq.sp(q, ""), ToolCall.tc_spell_gate(q), pre, tgq.sp_nil(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(tgq.G(i), ok)

def tgq.main(-i: String, d: Wr.Dec<Tc.Gate>, inv: tgq.Q(i, d), ok: {String.eq(FTc.ffi.gate(d), ToolCall.tc_bad_gate()) == False{} : Bool}) -> tgq.G(i):
  match d:
    case Wr.Got{+q, +r}:
      tgq.fin(i, q, r, inv, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(tgq.G(i), ok)

def ToolCall.tool_call_gate_reads_only_questions(i, other):
  tgq.main(i, FTc.get_gate(i), tgq.go(i, Wr.get_nat(i), {==}), other)
