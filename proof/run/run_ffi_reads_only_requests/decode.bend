# eukhe: lemmas of LAW run_ffi_reads_only_requests (also used by
# run_ffi_malformed_unless_request): whatever a decoder of the run entry
# reads is the grammar's spelling of what it read, then its rest, and its
# numbers fit the wire. Each stage carries the input spelled up to its
# field (`pre`); the wire's exactness laws turn a read Nat or Bool into its
# spelling (wire_nat_exact, wire_bool_exact) and a read Nat into one that
# fits (wire_nat_decoded_fits); an unknown tag is Bad, so it reads nothing.

import Base
import ../../../bend/ffi_run.bend as FRn
import ../../../bend/run/decision.bend as RnDecision
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/state.bend as RnState
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/run/entry.bend as Run
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def dk.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

def dk.and3(-a: Bool, -b: Bool, -c: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}, hc: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  LAWireSpell.ws_and_tt(a, Bool.and(b, c), ha, LAWireSpell.ws_and_tt(b, c, hb, hc))

def dk.and4(-a: Bool, -b: Bool, -c: Bool, -d: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}, hc: {c == True{} : Bool}, hd: {d == True{} : Bool}) -> {Bool.and(a, Bool.and(b, Bool.and(c, d))) == True{} : Bool}:
  LAWireSpell.ws_and_tt(a, Bool.and(b, Bool.and(c, d)), ha, dk.and3(b, c, d, hb, hc, hd))

# The limits
# ----------

def dk.Lim(s: String, d: Wr.Dec<RnDecision.Lim>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Run.run_spell_lim(l, r) : String} & {Run.run.lim_fits(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dk.lim.f3(+s: String, +a: Nat, +b: Nat, +c: Nat, +s3: String, pre: {s == Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, s3))) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> dk.Lim(s, FRn.get_lim.f3(a, b, c, d)):
  match d:
    case Wr.Got{+x, +s4}:
      +ee = ed
      (dk.step(z => Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, z))), s, s3, Wr.put_nat(x, s4), pre, Wire.wire_nat_exact(s3, x, s4, ee)), dk.and4(LawsBase.wire_fits(a), LawsBase.wire_fits(b), LawsBase.wire_fits(c), LawsBase.wire_fits(x), fa, fb, fc, Wire.wire_nat_decoded_fits(s3, x, s4, ee)))
    case Wr.Bad{}:
      Unit{}

def dk.lim.f2(+s: String, +a: Nat, +b: Nat, +s2: String, pre: {s == Wr.put_nat(a, Wr.put_nat(b, s2)) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> dk.Lim(s, FRn.get_lim.f2(a, b, d)):
  match d:
    case Wr.Got{+c, +s3}:
      +ee = ed
      dk.lim.f3(s, a, b, c, s3, dk.step(z => Wr.put_nat(a, Wr.put_nat(b, z)), s, s2, Wr.put_nat(c, s3), pre, Wire.wire_nat_exact(s2, c, s3, ee)), fa, fb, Wire.wire_nat_decoded_fits(s2, c, s3, ee), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def dk.lim.f1(+s: String, +a: Nat, +s1: String, pre: {s == Wr.put_nat(a, s1) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> dk.Lim(s, FRn.get_lim.f1(a, d)):
  match d:
    case Wr.Got{+b, +s2}:
      +ee = ed
      dk.lim.f2(s, a, b, s2, dk.step(z => Wr.put_nat(a, z), s, s1, Wr.put_nat(b, s2), pre, Wire.wire_nat_exact(s1, b, s2, ee)), fa, Wire.wire_nat_decoded_fits(s1, b, s2, ee), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dk.lim.f0(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.Lim(s, FRn.get_lim.f0(d)):
  match d:
    case Wr.Got{+a, +s1}:
      +ee = ed
      dk.lim.f1(s, a, s1, Wire.wire_nat_exact(s, a, s1, ee), Wire.wire_nat_decoded_fits(s, a, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def dk.lim(+s: String) -> dk.Lim(s, FRn.get_lim(s)):
  dk.lim.f0(s, Wr.get_nat(s), {==})

# The counts
# ----------

def dk.At(s: String, d: Wr.Dec<RnDecision.At>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Run.run_spell_at(t, r) : String} & {Run.run.at_fits(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dk.at.f3(+s: String, +a: Nat, +b: Nat, +c: Nat, +s3: String, pre: {s == Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, s3))) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == d : Wr.Dec<Bool>}) -> dk.At(s, FRn.get_at.f3(a, b, c, d)):
  match d:
    case Wr.Got{+x, +s4}:
      (dk.step(z => Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, z))), s, s3, Wr.put_bool(x, s4), pre, Wire.wire_bool_exact(s3, x, s4, ed)), dk.and3(LawsBase.wire_fits(a), LawsBase.wire_fits(b), LawsBase.wire_fits(c), fa, fb, fc))
    case Wr.Bad{}:
      Unit{}

def dk.at.f2(+s: String, +a: Nat, +b: Nat, +s2: String, pre: {s == Wr.put_nat(a, Wr.put_nat(b, s2)) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> dk.At(s, FRn.get_at.f2(a, b, d)):
  match d:
    case Wr.Got{+c, +s3}:
      +ee = ed
      dk.at.f3(s, a, b, c, s3, dk.step(z => Wr.put_nat(a, Wr.put_nat(b, z)), s, s2, Wr.put_nat(c, s3), pre, Wire.wire_nat_exact(s2, c, s3, ee)), fa, fb, Wire.wire_nat_decoded_fits(s2, c, s3, ee), Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def dk.at.f1(+s: String, +a: Nat, +s1: String, pre: {s == Wr.put_nat(a, s1) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> dk.At(s, FRn.get_at.f1(a, d)):
  match d:
    case Wr.Got{+b, +s2}:
      +ee = ed
      dk.at.f2(s, a, b, s2, dk.step(z => Wr.put_nat(a, z), s, s1, Wr.put_nat(b, s2), pre, Wire.wire_nat_exact(s1, b, s2, ee)), fa, Wire.wire_nat_decoded_fits(s1, b, s2, ee), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dk.at.f0(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.At(s, FRn.get_at.f0(d)):
  match d:
    case Wr.Got{+a, +s1}:
      +ee = ed
      dk.at.f1(s, a, s1, Wire.wire_nat_exact(s, a, s1, ee), Wire.wire_nat_decoded_fits(s, a, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def dk.at(+s: String) -> dk.At(s, FRn.get_at(s)):
  dk.at.f0(s, Wr.get_nat(s), {==})

# The reply
# ---------

def dk.Reply(s: String, d: Wr.Dec<RnState.Reply>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Run.run_spell_reply(x, r) : String}
    case Wr.Bad{}:
      Unit

def dk.reply.c3.f1(+s: String, +p: Bool, +s1: String, pre: {s == Wr.put_nat(3n, Wr.put_bool(p, s1)) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> dk.Reply(s, FRn.get_reply.c3.f1(p, d)):
  match d:
    case Wr.Got{+q, +s2}:
      dk.step(z => Wr.put_nat(3n, Wr.put_bool(p, z)), s, s1, Wr.put_bool(q, s2), pre, Wire.wire_bool_exact(s1, q, s2, ed))
    case Wr.Bad{}:
      Unit{}

def dk.reply.c3.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> dk.Reply(s, FRn.get_reply.c3.f0(d)):
  match d:
    case Wr.Got{+p, +s1}:
      dk.reply.c3.f1(s, p, s1, dk.step(z => Wr.put_nat(3n, z), s, s0, Wr.put_bool(p, s1), pre, Wire.wire_bool_exact(s0, p, s1, ed)), Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

def dk.reply.c4.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> dk.Reply(s, FRn.get_reply.c4.f0(d)):
  match d:
    case Wr.Got{+p, +s1}:
      dk.step(z => Wr.put_nat(4n, z), s, s0, Wr.put_bool(p, s1), pre, Wire.wire_bool_exact(s0, p, s1, ed))
    case Wr.Bad{}:
      Unit{}

def dk.reply.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.Reply(s, FRn.get_reply.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n:
          dk.reply.c3.f0(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_bool(s0), {==})
        case 4n:
          dk.reply.c4.f0(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), Wr.get_bool(s0), {==})
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dk.reply(+s: String) -> dk.Reply(s, FRn.get_reply(s)):
  dk.reply.go(s, Wr.get_nat(s), {==})

# The message that ended a turn
# -----------------------------

def dk.Ended(s: String, d: Wr.Dec<RnState.Ended>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Run.run_spell_ended(m, r) : String}
    case Wr.Bad{}:
      Unit

def dk.ended.f1(+s: String, +p: Bool, +s1: String, pre: {s == Wr.put_bool(p, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> dk.Ended(s, FRn.get_ended.f1(p, d)):
  match d:
    case Wr.Got{+q, +s2}:
      dk.step(z => Wr.put_bool(p, z), s, s1, Wr.put_bool(q, s2), pre, Wire.wire_bool_exact(s1, q, s2, ed))
    case Wr.Bad{}:
      Unit{}

def dk.ended.f0(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> dk.Ended(s, FRn.get_ended.f0(d)):
  match d:
    case Wr.Got{+p, +s1}:
      dk.ended.f1(s, p, s1, Wire.wire_bool_exact(s, p, s1, ed), Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

def dk.ended(+s: String) -> dk.Ended(s, FRn.get_ended(s)):
  dk.ended.f0(s, Wr.get_bool(s), {==})

# The threshold and the compaction's end
# --------------------------------------

def dk.Th(s: String, d: Wr.Dec<RnDecision.Th>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Run.run_spell_th(x, r) : String}
    case Wr.Bad{}:
      Unit

def dk.th.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.Th(s, FRn.get_th.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dk.th(+s: String) -> dk.Th(s, FRn.get_th(s)):
  dk.th.go(s, Wr.get_nat(s), {==})

def dk.Got(s: String, d: Wr.Dec<RnState.Got>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Run.run_spell_got(x, r) : String}
    case Wr.Bad{}:
      Unit

def dk.got.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.Got(s, FRn.get_got.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dk.got(+s: String) -> dk.Got(s, FRn.get_got(s)):
  dk.got.go(s, Wr.get_nat(s), {==})

# The recovery caps, the stuck reply, the recovery of the note
# ------------------------------------------------------------

def dk.RCfg(s: String, d: Wr.Dec<RnRecovery.RCfg>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == Run.run_spell_rcfg(c, r) : String} & {Run.run.rcfg_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dk.rcfg.f3(+s: String, +a: Nat, +b: Nat, +c: Nat, +s3: String, pre: {s == Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, s3))) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> dk.RCfg(s, FRn.get_rcfg.f3(a, b, c, d)):
  match d:
    case Wr.Got{+x, +s4}:
      +ee = ed
      (dk.step(z => Wr.put_nat(a, Wr.put_nat(b, Wr.put_nat(c, z))), s, s3, Wr.put_nat(x, s4), pre, Wire.wire_nat_exact(s3, x, s4, ee)), dk.and4(LawsBase.wire_fits(a), LawsBase.wire_fits(b), LawsBase.wire_fits(c), LawsBase.wire_fits(x), fa, fb, fc, Wire.wire_nat_decoded_fits(s3, x, s4, ee)))
    case Wr.Bad{}:
      Unit{}

def dk.rcfg.f2(+s: String, +a: Nat, +b: Nat, +s2: String, pre: {s == Wr.put_nat(a, Wr.put_nat(b, s2)) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> dk.RCfg(s, FRn.get_rcfg.f2(a, b, d)):
  match d:
    case Wr.Got{+c, +s3}:
      +ee = ed
      dk.rcfg.f3(s, a, b, c, s3, dk.step(z => Wr.put_nat(a, Wr.put_nat(b, z)), s, s2, Wr.put_nat(c, s3), pre, Wire.wire_nat_exact(s2, c, s3, ee)), fa, fb, Wire.wire_nat_decoded_fits(s2, c, s3, ee), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def dk.rcfg.f1(+s: String, +a: Nat, +s1: String, pre: {s == Wr.put_nat(a, s1) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> dk.RCfg(s, FRn.get_rcfg.f1(a, d)):
  match d:
    case Wr.Got{+b, +s2}:
      +ee = ed
      dk.rcfg.f2(s, a, b, s2, dk.step(z => Wr.put_nat(a, z), s, s1, Wr.put_nat(b, s2), pre, Wire.wire_nat_exact(s1, b, s2, ee)), fa, Wire.wire_nat_decoded_fits(s1, b, s2, ee), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dk.rcfg.f0(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.RCfg(s, FRn.get_rcfg.f0(d)):
  match d:
    case Wr.Got{+a, +s1}:
      +ee = ed
      dk.rcfg.f1(s, a, s1, Wire.wire_nat_exact(s, a, s1, ee), Wire.wire_nat_decoded_fits(s, a, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def dk.rcfg(+s: String) -> dk.RCfg(s, FRn.get_rcfg(s)):
  dk.rcfg.f0(s, Wr.get_nat(s), {==})

def dk.Stuck(s: String, d: Wr.Dec<RnDecision.Stuck>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Run.run_spell_stuck(x, r) : String} & {Run.run.stuck_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dk.stuck.c2.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> dk.Stuck(s, FRn.get_stuck.c2.f0(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +ee = ed
      (dk.step(z => Wr.put_nat(2n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, ee)), Wire.wire_nat_decoded_fits(s0, x, s1, ee))
    case Wr.Bad{}:
      Unit{}

def dk.stuck.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.Stuck(s, FRn.get_stuck.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          (Wire.wire_nat_exact(s, 1n, s0, ed), {==})
        case 2n:
          dk.stuck.c2.f0(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_nat(s0), {==})
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dk.stuck(+s: String) -> dk.Stuck(s, FRn.get_stuck(s)):
  dk.stuck.go(s, Wr.get_nat(s), {==})

def dk.Rk(s: String, d: Wr.Dec<RnRecovery.Rk>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Run.run_spell_rk(x, r) : String}
    case Wr.Bad{}:
      Unit

def dk.rk.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.Rk(s, FRn.get_rk.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s0, ed)
        case 4n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def dk.rk(+s: String) -> dk.Rk(s, FRn.get_rk(s)):
  dk.rk.go(s, Wr.get_nat(s), {==})

# The request
# -----------

def dk.Ask(s: String, d: Wr.Dec<FRn.Ask>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Run.run_spell_ask(a, r) : String} & {Run.run.ask_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a reply: the limits, the counts, the reply
def dk.c0.f2(+s: String, +l: RnDecision.Lim, +t: RnDecision.At, +s2: String, pre: {s == Wr.put_nat(0n, Run.run_spell_lim(l, Run.run_spell_at(t, s2))) : String}, fl: {Run.run.lim_fits(l) == True{} : Bool}, ft: {Run.run.at_fits(t) == True{} : Bool}, d: Wr.Dec<RnState.Reply>, xd: dk.Reply(s2, d)) -> dk.Ask(s, FRn.get_ask.c0.f2(l, t, d)):
  match d:
    case Wr.Got{+reply, +s3}:
      (dk.step(z => Wr.put_nat(0n, Run.run_spell_lim(l, Run.run_spell_at(t, z))), s, s2, Run.run_spell_reply(reply, s3), pre, xd), LAWireSpell.ws_and_tt(Run.run.lim_fits(l), Run.run.at_fits(t), fl, ft))
    case Wr.Bad{}:
      Unit{}

def dk.c0.f1(+s: String, +l: RnDecision.Lim, +s1: String, pre: {s == Wr.put_nat(0n, Run.run_spell_lim(l, s1)) : String}, fl: {Run.run.lim_fits(l) == True{} : Bool}, d: Wr.Dec<RnDecision.At>, xd: dk.At(s1, d)) -> dk.Ask(s, FRn.get_ask.c0.f1(l, d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e2, ft) = xd
      dk.c0.f2(s, l, t, s2, dk.step(z => Wr.put_nat(0n, Run.run_spell_lim(l, z)), s, s1, Run.run_spell_at(t, s2), pre, e2), fl, ft, FRn.get_reply(s2), dk.reply(s2))
    case Wr.Bad{}:
      Unit{}

def dk.c0.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<RnDecision.Lim>, xd: dk.Lim(s0, d)) -> dk.Ask(s, FRn.get_ask.c0.f0(d)):
  match d:
    case Wr.Got{+l, +s1}:
      (e1, fl) = xd
      dk.c0.f1(s, l, s1, dk.step(z => Wr.put_nat(0n, z), s, s0, Run.run_spell_lim(l, s1), pre, e1), fl, FRn.get_at(s1), dk.at(s1))
    case Wr.Bad{}:
      Unit{}

# a message that ended a turn
def dk.c1.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<RnState.Ended>, xd: dk.Ended(s0, d)) -> dk.Ask(s, FRn.get_ask.c1.f0(d)):
  match d:
    case Wr.Got{+m, +s1}:
      (dk.step(z => Wr.put_nat(1n, z), s, s0, Run.run_spell_ended(m, s1), pre, xd), {==})
    case Wr.Bad{}:
      Unit{}

# a preparation: compacted, the threshold
def dk.c2.f1(+s: String, +p: Bool, +s1: String, pre: {s == Wr.put_nat(2n, Wr.put_bool(p, s1)) : String}, d: Wr.Dec<RnDecision.Th>, xd: dk.Th(s1, d)) -> dk.Ask(s, FRn.get_ask.c2.f1(p, d)):
  match d:
    case Wr.Got{+th, +s2}:
      (dk.step(z => Wr.put_nat(2n, Wr.put_bool(p, z)), s, s1, Run.run_spell_th(th, s2), pre, xd), {==})
    case Wr.Bad{}:
      Unit{}

def dk.c2.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> dk.Ask(s, FRn.get_ask.c2.f0(d)):
  match d:
    case Wr.Got{+p, +s1}:
      dk.c2.f1(s, p, s1, dk.step(z => Wr.put_nat(2n, z), s, s0, Wr.put_bool(p, s1), pre, Wire.wire_bool_exact(s0, p, s1, ed)), FRn.get_th(s1), dk.th(s1))
    case Wr.Bad{}:
      Unit{}

# a compaction's end: an overflow's, how it ended
def dk.c3.f1(+s: String, +p: Bool, +s1: String, pre: {s == Wr.put_nat(3n, Wr.put_bool(p, s1)) : String}, d: Wr.Dec<RnState.Got>, xd: dk.Got(s1, d)) -> dk.Ask(s, FRn.get_ask.c3.f1(p, d)):
  match d:
    case Wr.Got{+got, +s2}:
      (dk.step(z => Wr.put_nat(3n, Wr.put_bool(p, z)), s, s1, Run.run_spell_got(got, s2), pre, xd), {==})
    case Wr.Bad{}:
      Unit{}

def dk.c3.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> dk.Ask(s, FRn.get_ask.c3.f0(d)):
  match d:
    case Wr.Got{+p, +s1}:
      dk.c3.f1(s, p, s1, dk.step(z => Wr.put_nat(3n, z), s, s0, Wr.put_bool(p, s1), pre, Wire.wire_bool_exact(s0, p, s1, ed)), FRn.get_got(s1), dk.got(s1))
    case Wr.Bad{}:
      Unit{}

# a round's end: the limits, the rounds, a control, a reset
def dk.c4.f3(+s: String, +l: RnDecision.Lim, +count: Nat, +stops: Bool, +s3: String, pre: {s == Wr.put_nat(4n, Run.run_spell_lim(l, Wr.put_nat(count, Wr.put_bool(stops, s3)))) : String}, fl: {Run.run.lim_fits(l) == True{} : Bool}, fc: {LawsBase.wire_fits(count) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == d : Wr.Dec<Bool>}) -> dk.Ask(s, FRn.get_ask.c4.f3(l, count, stops, d)):
  match d:
    case Wr.Got{+reset, +s4}:
      (dk.step(z => Wr.put_nat(4n, Run.run_spell_lim(l, Wr.put_nat(count, Wr.put_bool(stops, z)))), s, s3, Wr.put_bool(reset, s4), pre, Wire.wire_bool_exact(s3, reset, s4, ed)), LAWireSpell.ws_and_tt(Run.run.lim_fits(l), LawsBase.wire_fits(count), fl, fc))
    case Wr.Bad{}:
      Unit{}

def dk.c4.f2(+s: String, +l: RnDecision.Lim, +count: Nat, +s2: String, pre: {s == Wr.put_nat(4n, Run.run_spell_lim(l, Wr.put_nat(count, s2))) : String}, fl: {Run.run.lim_fits(l) == True{} : Bool}, fc: {LawsBase.wire_fits(count) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> dk.Ask(s, FRn.get_ask.c4.f2(l, count, d)):
  match d:
    case Wr.Got{+stops, +s3}:
      dk.c4.f3(s, l, count, stops, s3, dk.step(z => Wr.put_nat(4n, Run.run_spell_lim(l, Wr.put_nat(count, z))), s, s2, Wr.put_bool(stops, s3), pre, Wire.wire_bool_exact(s2, stops, s3, ed)), fl, fc, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def dk.c4.f1(+s: String, +l: RnDecision.Lim, +s1: String, pre: {s == Wr.put_nat(4n, Run.run_spell_lim(l, s1)) : String}, fl: {Run.run.lim_fits(l) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> dk.Ask(s, FRn.get_ask.c4.f1(l, d)):
  match d:
    case Wr.Got{+count, +s2}:
      +ee = ed
      dk.c4.f2(s, l, count, s2, dk.step(z => Wr.put_nat(4n, Run.run_spell_lim(l, z)), s, s1, Wr.put_nat(count, s2), pre, Wire.wire_nat_exact(s1, count, s2, ee)), fl, Wire.wire_nat_decoded_fits(s1, count, s2, ee), Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dk.c4.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<RnDecision.Lim>, xd: dk.Lim(s0, d)) -> dk.Ask(s, FRn.get_ask.c4.f0(d)):
  match d:
    case Wr.Got{+l, +s1}:
      (e1, fl) = xd
      dk.c4.f1(s, l, s1, dk.step(z => Wr.put_nat(4n, z), s, s0, Run.run_spell_lim(l, s1), pre, e1), fl, Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a recovery: the caps, the stuck reply, the recovery of the note, its row
def dk.c5.f3(+s: String, +rc: RnRecovery.RCfg, +st: RnDecision.Stuck, +k: RnRecovery.Rk, +s3: String, pre: {s == Wr.put_nat(5n, Run.run_spell_rcfg(rc, Run.run_spell_stuck(st, Run.run_spell_rk(k, s3)))) : String}, fr: {Run.run.rcfg_fits(rc) == True{} : Bool}, fs: {Run.run.stuck_fits(st) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> dk.Ask(s, FRn.get_ask.c5.f3(rc, st, k, d)):
  match d:
    case Wr.Got{+row, +s4}:
      +ee = ed
      (dk.step(z => Wr.put_nat(5n, Run.run_spell_rcfg(rc, Run.run_spell_stuck(st, Run.run_spell_rk(k, z)))), s, s3, Wr.put_nat(row, s4), pre, Wire.wire_nat_exact(s3, row, s4, ee)), dk.and3(Run.run.rcfg_fits(rc), Run.run.stuck_fits(st), LawsBase.wire_fits(row), fr, fs, Wire.wire_nat_decoded_fits(s3, row, s4, ee)))
    case Wr.Bad{}:
      Unit{}

def dk.c5.f2(+s: String, +rc: RnRecovery.RCfg, +st: RnDecision.Stuck, +s2: String, pre: {s == Wr.put_nat(5n, Run.run_spell_rcfg(rc, Run.run_spell_stuck(st, s2))) : String}, fr: {Run.run.rcfg_fits(rc) == True{} : Bool}, fs: {Run.run.stuck_fits(st) == True{} : Bool}, d: Wr.Dec<RnRecovery.Rk>, xd: dk.Rk(s2, d)) -> dk.Ask(s, FRn.get_ask.c5.f2(rc, st, d)):
  match d:
    case Wr.Got{+k, +s3}:
      dk.c5.f3(s, rc, st, k, s3, dk.step(z => Wr.put_nat(5n, Run.run_spell_rcfg(rc, Run.run_spell_stuck(st, z))), s, s2, Run.run_spell_rk(k, s3), pre, xd), fr, fs, Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def dk.c5.f1(+s: String, +rc: RnRecovery.RCfg, +s1: String, pre: {s == Wr.put_nat(5n, Run.run_spell_rcfg(rc, s1)) : String}, fr: {Run.run.rcfg_fits(rc) == True{} : Bool}, d: Wr.Dec<RnDecision.Stuck>, xd: dk.Stuck(s1, d)) -> dk.Ask(s, FRn.get_ask.c5.f1(rc, d)):
  match d:
    case Wr.Got{+st, +s2}:
      (e2, fs) = xd
      dk.c5.f2(s, rc, st, s2, dk.step(z => Wr.put_nat(5n, Run.run_spell_rcfg(rc, z)), s, s1, Run.run_spell_stuck(st, s2), pre, e2), fr, fs, FRn.get_rk(s2), dk.rk(s2))
    case Wr.Bad{}:
      Unit{}

def dk.c5.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(5n, s0) : String}, d: Wr.Dec<RnRecovery.RCfg>, xd: dk.RCfg(s0, d)) -> dk.Ask(s, FRn.get_ask.c5.f0(d)):
  match d:
    case Wr.Got{+rc, +s1}:
      (e1, fr) = xd
      dk.c5.f1(s, rc, s1, dk.step(z => Wr.put_nat(5n, z), s, s0, Run.run_spell_rcfg(rc, s1), pre, e1), fr, FRn.get_stuck(s1), dk.stuck(s1))
    case Wr.Bad{}:
      Unit{}

# a failed poll: retryable, the failures, the retries
def dk.c6.f2(+s: String, +p: Bool, +x: Nat, +s2: String, pre: {s == Wr.put_nat(6n, Wr.put_bool(p, Wr.put_nat(x, s2))) : String}, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> dk.Ask(s, FRn.get_ask.c6.f2(p, x, d)):
  match d:
    case Wr.Got{+y, +s3}:
      +ee = ed
      (dk.step(z => Wr.put_nat(6n, Wr.put_bool(p, Wr.put_nat(x, z))), s, s2, Wr.put_nat(y, s3), pre, Wire.wire_nat_exact(s2, y, s3, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_fits(y), fx, Wire.wire_nat_decoded_fits(s2, y, s3, ee)))
    case Wr.Bad{}:
      Unit{}

def dk.c6.f1(+s: String, +p: Bool, +s1: String, pre: {s == Wr.put_nat(6n, Wr.put_bool(p, s1)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> dk.Ask(s, FRn.get_ask.c6.f1(p, d)):
  match d:
    case Wr.Got{+x, +s2}:
      +ee = ed
      dk.c6.f2(s, p, x, s2, dk.step(z => Wr.put_nat(6n, Wr.put_bool(p, z)), s, s1, Wr.put_nat(x, s2), pre, Wire.wire_nat_exact(s1, x, s2, ee)), Wire.wire_nat_decoded_fits(s1, x, s2, ee), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dk.c6.f0(+s: String, +s0: String, pre: {s == Wr.put_nat(6n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> dk.Ask(s, FRn.get_ask.c6.f0(d)):
  match d:
    case Wr.Got{+p, +s1}:
      dk.c6.f1(s, p, s1, dk.step(z => Wr.put_nat(6n, z), s, s0, Wr.put_bool(p, s1), pre, Wire.wire_bool_exact(s0, p, s1, ed)), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def dk.ask.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dk.Ask(s, FRn.get_ask.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          dk.c0.f0(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FRn.get_lim(s0), dk.lim(s0))
        case 1n:
          dk.c1.f0(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FRn.get_ended(s0), dk.ended(s0))
        case 2n:
          dk.c2.f0(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_bool(s0), {==})
        case 3n:
          dk.c3.f0(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_bool(s0), {==})
        case 4n:
          dk.c4.f0(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), FRn.get_lim(s0), dk.lim(s0))
        case 5n:
          dk.c5.f0(s, s0, Wire.wire_nat_exact(s, 5n, s0, ed), FRn.get_rcfg(s0), dk.rcfg(s0))
        case 6n:
          dk.c6.f0(s, s0, Wire.wire_nat_exact(s, 6n, s0, ed), Wr.get_bool(s0), {==})
        case 7n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def dk.ask(+s: String) -> dk.Ask(s, FRn.get_ask(s)):
  dk.ask.go(s, Wr.get_nat(s), {==})
