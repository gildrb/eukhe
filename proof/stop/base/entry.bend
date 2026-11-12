# eukhe: lemmas of LAW stop_entry_reads_only_spelled: a predicate per
# answer of the entry's reader (sre.Q: what it read is the input), carried
# field by field with the wire's exactness laws (wire_nat_exact,
# wire_bool_exact: a decoded value is exactly its spelling, then the rest)

import Base
import ../../../bend/ffi_stop.bend as FS
import ../../../bend/wire.bend as Wr
import ../../../laws/stop.bend as Stop
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_bool_exact.bend as PWireBoolExact

# the reader's answer d to the input s: a request read is s spelled
def sre.Q(d: Wr.Dec<FS.Ask>, s: String) -> Type:
  match d:
    case Wr.Got{a, rest}:
      {s == Stop.sp_w_ask(a, rest) : String}
    case Wr.Bad{}:
      Unit

# s spelled up to a field a is s spelled up to its spelling b
def sre.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# The walk: cut, text, broken, pending, then the window's facts: window,
# catalog, prompt, out, cuttable
# ----------------------------------------------------------------------

def sre.walk9(+s: String, +c: Bool, +t: Bool, +b: Bool, +p: Bool, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, Wr.put_nat(ca, Wr.put_nat(pr, Wr.put_nat(o, r))))))))) : String}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(r) == d : Wr.Dec<Bool>}) -> sre.Q(FS.get_walk.cuttable(c, t, b, p, w, ca, pr, o, d), s):
  match d:
    case Wr.Got{+cu, +r9}:
      sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, Wr.put_nat(ca, Wr.put_nat(pr, Wr.put_nat(o, z))))))))), s, r, Wr.put_bool(cu, r9), pre, Wire.wire_bool_exact(r, cu, r9, ed))
    case Wr.Bad{}:
      Unit{}

def sre.walk8(+s: String, +c: Bool, +t: Bool, +b: Bool, +p: Bool, +w: Nat, +ca: Nat, +pr: Nat, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, Wr.put_nat(ca, Wr.put_nat(pr, r)))))))) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_walk.out(c, t, b, p, w, ca, pr, d), s):
  match d:
    case Wr.Got{+o, +r8}:
      sre.walk9(s, c, t, b, p, w, ca, pr, o, r8, sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, Wr.put_nat(ca, Wr.put_nat(pr, z)))))))), s, r, Wr.put_nat(o, r8), pre, Wire.wire_nat_exact(r, o, r8, ed)), Wr.get_bool(r8), {==})
    case Wr.Bad{}:
      Unit{}

def sre.walk7(+s: String, +c: Bool, +t: Bool, +b: Bool, +p: Bool, +w: Nat, +ca: Nat, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, Wr.put_nat(ca, r))))))) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_walk.prompt(c, t, b, p, w, ca, d), s):
  match d:
    case Wr.Got{+pr, +r7}:
      sre.walk8(s, c, t, b, p, w, ca, pr, r7, sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, Wr.put_nat(ca, z))))))), s, r, Wr.put_nat(pr, r7), pre, Wire.wire_nat_exact(r, pr, r7, ed)), Wr.get_nat(r7), {==})
    case Wr.Bad{}:
      Unit{}

def sre.walk6(+s: String, +c: Bool, +t: Bool, +b: Bool, +p: Bool, +w: Nat, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, r)))))) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_walk.catalog(c, t, b, p, w, d), s):
  match d:
    case Wr.Got{+ca, +r6}:
      sre.walk7(s, c, t, b, p, w, ca, r6, sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, Wr.put_nat(w, z)))))), s, r, Wr.put_nat(ca, r6), pre, Wire.wire_nat_exact(r, ca, r6, ed)), Wr.get_nat(r6), {==})
    case Wr.Bad{}:
      Unit{}

def sre.walk5(+s: String, +c: Bool, +t: Bool, +b: Bool, +p: Bool, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, r))))) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_walk.window(c, t, b, p, d), s):
  match d:
    case Wr.Got{+w, +r5}:
      sre.walk6(s, c, t, b, p, w, r5, sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, Wr.put_bool(p, z))))), s, r, Wr.put_nat(w, r5), pre, Wire.wire_nat_exact(r, w, r5, ed)), Wr.get_nat(r5), {==})
    case Wr.Bad{}:
      Unit{}

def sre.walk4(+s: String, +c: Bool, +t: Bool, +b: Bool, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, r)))) : String}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(r) == d : Wr.Dec<Bool>}) -> sre.Q(FS.get_walk.pending(c, t, b, d), s):
  match d:
    case Wr.Got{+p, +r4}:
      sre.walk5(s, c, t, b, p, r4, sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, z)))), s, r, Wr.put_bool(p, r4), pre, Wire.wire_bool_exact(r, p, r4, ed)), Wr.get_nat(r4), {==})
    case Wr.Bad{}:
      Unit{}

def sre.walk3(+s: String, +c: Bool, +t: Bool, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, r))) : String}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(r) == d : Wr.Dec<Bool>}) -> sre.Q(FS.get_walk.broken(c, t, d), s):
  match d:
    case Wr.Got{+b, +r3}:
      sre.walk4(s, c, t, b, r3, sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, z))), s, r, Wr.put_bool(b, r3), pre, Wire.wire_bool_exact(r, b, r3, ed)), Wr.get_bool(r3), {==})
    case Wr.Bad{}:
      Unit{}

def sre.walk2(+s: String, +c: Bool, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, r)) : String}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(r) == d : Wr.Dec<Bool>}) -> sre.Q(FS.get_walk.text(c, d), s):
  match d:
    case Wr.Got{+t, +r2}:
      sre.walk3(s, c, t, r2, sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, z)), s, r, Wr.put_bool(t, r2), pre, Wire.wire_bool_exact(r, t, r2, ed)), Wr.get_bool(r2), {==})
    case Wr.Bad{}:
      Unit{}

def sre.walk1(+s: String, +r: String, +pre: {s == Wr.put_nat(0n, r) : String}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(r) == d : Wr.Dec<Bool>}) -> sre.Q(FS.get_walk(d), s):
  match d:
    case Wr.Got{+c, +r1}:
      sre.walk2(s, c, r1, sre.step(z => Wr.put_nat(0n, z), s, r, Wr.put_bool(c, r1), pre, Wire.wire_bool_exact(r, c, r1, ed)), Wr.get_bool(r1), {==})
    case Wr.Bad{}:
      Unit{}

# The round note: max, done
# -------------------------

def sre.rounds2(+s: String, +m: Nat, +r: String, +pre: {s == Wr.put_nat(1n, Wr.put_nat(m, r)) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_rounds.done(m, d), s):
  match d:
    case Wr.Got{+n, +r2}:
      sre.step(z => Wr.put_nat(1n, Wr.put_nat(m, z)), s, r, Wr.put_nat(n, r2), pre, Wire.wire_nat_exact(r, n, r2, ed))
    case Wr.Bad{}:
      Unit{}

def sre.rounds1(+s: String, +r: String, +pre: {s == Wr.put_nat(1n, r) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_rounds(d), s):
  match d:
    case Wr.Got{+m, +r1}:
      sre.rounds2(s, m, r1, sre.step(z => Wr.put_nat(1n, z), s, r, Wr.put_nat(m, r1), pre, Wire.wire_nat_exact(r, m, r1, ed)), Wr.get_nat(r1), {==})
    case Wr.Bad{}:
      Unit{}

# The tag
# -------

def sre.tag(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_ask.tag(d), s):
  match d:
    case Wr.Got{+n, +r}:
      match n:
        case 0n:
          sre.walk1(s, r, Wire.wire_nat_exact(s, 0n, r, ed), Wr.get_bool(r), {==})
        case 1n:
          sre.rounds1(s, r, Wire.wire_nat_exact(s, 1n, r, ed), Wr.get_nat(r), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}
