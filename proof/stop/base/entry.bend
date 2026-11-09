# eukhe: lemmas of LAW stop_entry_reads_only_spelled: a predicate per
# answer of the entry's reader (sre.Q: what it read is the input), carried
# field by field with the wire's exactness laws (wire_nat_exact,
# wire_bool_exact: a decoded value is exactly its spelling, then the rest)

import Base
import ../../../bend/stop.bend as S
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

# The walk: cut, text, broken, pending
# ------------------------------------

def sre.walk4(+s: String, +c: Bool, +t: Bool, +b: Bool, +r: String, +pre: {s == Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, r)))) : String}, d: Wr.Dec<Bool>, +ed: {Wr.get_bool(r) == d : Wr.Dec<Bool>}) -> sre.Q(FS.get_walk.pending(c, t, b, d), s):
  match d:
    case Wr.Got{+p, +r4}:
      sre.step(z => Wr.put_nat(0n, Wr.put_bool(c, Wr.put_bool(t, Wr.put_bool(b, z)))), s, r, Wr.put_bool(p, r4), pre, Wire.wire_bool_exact(r, p, r4, ed))
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

# The length note: attempt, tokens, row, cap
# ------------------------------------------

def sre.note4(+s: String, +a: Nat, +t: Nat, +w: Nat, +r: String, +pre: {s == Wr.put_nat(1n, Wr.put_nat(a, Wr.put_nat(t, Wr.put_nat(w, r)))) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_cut.cap(a, t, w, d), s):
  match d:
    case Wr.Got{+k, +r4}:
      sre.step(z => Wr.put_nat(1n, Wr.put_nat(a, Wr.put_nat(t, Wr.put_nat(w, z)))), s, r, Wr.put_nat(k, r4), pre, Wire.wire_nat_exact(r, k, r4, ed))
    case Wr.Bad{}:
      Unit{}

def sre.note3(+s: String, +a: Nat, +t: Nat, +r: String, +pre: {s == Wr.put_nat(1n, Wr.put_nat(a, Wr.put_nat(t, r))) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_cut.row(a, t, d), s):
  match d:
    case Wr.Got{+w, +r3}:
      sre.note4(s, a, t, w, r3, sre.step(z => Wr.put_nat(1n, Wr.put_nat(a, Wr.put_nat(t, z))), s, r, Wr.put_nat(w, r3), pre, Wire.wire_nat_exact(r, w, r3, ed)), Wr.get_nat(r3), {==})
    case Wr.Bad{}:
      Unit{}

def sre.note2(+s: String, +a: Nat, +r: String, +pre: {s == Wr.put_nat(1n, Wr.put_nat(a, r)) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_cut(a, d), s):
  match d:
    case Wr.Got{+t, +r2}:
      sre.note3(s, a, t, r2, sre.step(z => Wr.put_nat(1n, Wr.put_nat(a, z)), s, r, Wr.put_nat(t, r2), pre, Wire.wire_nat_exact(r, t, r2, ed)), Wr.get_nat(r2), {==})
    case Wr.Bad{}:
      Unit{}

def sre.note1(+s: String, +r: String, +pre: {s == Wr.put_nat(1n, r) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_note(d), s):
  match d:
    case Wr.Got{+a, +r1}:
      sre.note2(s, a, r1, sre.step(z => Wr.put_nat(1n, z), s, r, Wr.put_nat(a, r1), pre, Wire.wire_nat_exact(r, a, r1, ed)), Wr.get_nat(r1), {==})
    case Wr.Bad{}:
      Unit{}

# The round note: max, done
# -------------------------

def sre.rounds2(+s: String, +m: Nat, +r: String, +pre: {s == Wr.put_nat(2n, Wr.put_nat(m, r)) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_rounds.done(m, d), s):
  match d:
    case Wr.Got{+n, +r2}:
      sre.step(z => Wr.put_nat(2n, Wr.put_nat(m, z)), s, r, Wr.put_nat(n, r2), pre, Wire.wire_nat_exact(r, n, r2, ed))
    case Wr.Bad{}:
      Unit{}

def sre.rounds1(+s: String, +r: String, +pre: {s == Wr.put_nat(2n, r) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(r) == d : Wr.Dec<Nat>}) -> sre.Q(FS.get_rounds(d), s):
  match d:
    case Wr.Got{+m, +r1}:
      sre.rounds2(s, m, r1, sre.step(z => Wr.put_nat(2n, z), s, r, Wr.put_nat(m, r1), pre, Wire.wire_nat_exact(r, m, r1, ed)), Wr.get_nat(r1), {==})
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
          sre.note1(s, r, Wire.wire_nat_exact(s, 1n, r, ed), Wr.get_nat(r), {==})
        case 2n:
          sre.rounds1(s, r, Wire.wire_nat_exact(s, 2n, r, ed), Wr.get_nat(r), {==})
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}
