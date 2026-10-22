# ffi_wire: the wire round trip through the compiled Bend core, for the
# Rust test of crates/eukhe-bend (no rule): the request is a Nat, a U32, a
# Bool, a String and a List of Nats; the reply is the same values as Bend
# reads them, written again by bend/wire.bend's encoders (so the reply
# equals the request exactly when Bend reads back what Rust wrote). A
# malformed request, or input left over, answers the error form.

import Base
import ./wire.bend as W

def bad() -> String:
  W.err("malformed wire request")

def at.end(r: W.Dec<List<&2, Nat>>, n: Nat, x: U32, b: Bool, a: String) -> String:
  match r:
    case W.Got{xs, s}:
      match s:
        case SNil{}:
          W.put_nat(n, W.put_u32(x, W.put_bool(b, W.put_str(a, W.put_list(~Nat, ~W.put_nat, xs, "")))))
        case SCon{c, t}:
          bad()
    case W.Bad{}:
      bad()

def at.str(r: W.Dec<String>, n: Nat, x: U32, b: Bool) -> String:
  match r:
    case W.Got{a, s}:
      at.end(W.get_list(~Nat, ~W.get_nat, s), n, x, b, a)
    case W.Bad{}:
      bad()

def at.bool(r: W.Dec<Bool>, n: Nat, x: U32) -> String:
  match r:
    case W.Got{b, s}:
      at.str(W.get_str(s), n, x, b)
    case W.Bad{}:
      bad()

def at.u32(r: W.Dec<U32>, n: Nat) -> String:
  match r:
    case W.Got{x, s}:
      at.bool(W.get_bool(s), n, x)
    case W.Bad{}:
      bad()

def at.nat(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{n, s}:
      at.u32(W.get_u32(s), n)
    case W.Bad{}:
      bad()

def ffi(input: String) -> String:
  at.nat(W.get_nat(input))
