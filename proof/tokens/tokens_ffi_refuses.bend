# eukhe: the proof of LAW tokens_ffi_refuses
# The entry reads a tag (Wr.get_nat): malformed, or a tag other than 0,
# is the error form; tag 0 with input after it too. Tag 0 with nothing
# after it is the input put_nat(0, "") (the wire's wire_nat_exact), which
# is "0,", refuted by the premise.

import Base
import ../../bend/ffi_tokens.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/tokens.bend as Tokens
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact

def tfr.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def tfr.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : tfr.BD(_, Unit, A)
  Unit{}

def tfr.end(+s: String, rest: String, ex: {s == Wr.put_nat(0n, rest) : String}, no: {String.eq(s, "0,") == False{} : Bool}) -> {FT.run.end(Wr.end(rest)) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}:
  match rest:
    case SNil{}:
      tfr.absurd({FT.run.end(Wr.end(SNil{})) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}, Equal.trans(Bool, True{}, String.eq(s, "0,"), False{}, Equal.cong(String, Bool, x => String.eq(x, "0,"), Wr.put_nat(0n, SNil{}), s, Equal.sym(String, s, Wr.put_nat(0n, SNil{}), ex)), no))
    case SCon{c, t}:
      {==}

def tfr.tag(+s: String, t: Nat, +rest: String, ex: {s == Wr.put_nat(t, rest) : String}, no: {String.eq(s, "0,") == False{} : Bool}) -> {FT.run.tag(t, rest) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}:
  match t:
    case 0n:
      tfr.end(s, rest, ex, no)
    case 1n+p:
      {==}

def tfr.go(+s: String, r: Wr.Dec<Nat>, e: {Wr.get_nat(s) == r : Wr.Dec<Nat>}, no: {String.eq(s, "0,") == False{} : Bool}) -> {FT.run(r) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}:
  match r:
    case Wr.Got{+t, +rest}:
      tfr.tag(s, t, rest, Wire.wire_nat_exact(s, t, rest, e), no)
    case Wr.Bad{}:
      {==}

def Tokens.tokens_ffi_refuses(s, no):
  tfr.go(s, Wr.get_nat(s), {==}, no)
