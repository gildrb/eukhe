# eukhe: the proof of LAW tokens_ffi_malformed_exact
# The entry and the laws' reader read the same tag and end: where the
# reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_tokens.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/tokens.bend as Tokens

def tme.if_true(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def tme.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : tme.if_true(_, G)
  Unit{}

def tme.end(b: Bool, no: {b == False{} : Bool}) -> {FT.run.end(b) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}:
  match b:
    case True{}:
      tme.absurd({FT.run.end(True{}) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}, Equal.sym(Bool, True{}, False{}, no))
    case False{}:
      {==}

def tme.tag(t: Nat, s: String, no: {Tokens.read_req.tag(t, s) == False{} : Bool}) -> {FT.run.tag(t, s) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}:
  match t:
    case 0n:
      tme.end(Wr.end(s), no)
    case 1n+p:
      {==}

def tme.go(r: Wr.Dec<Nat>, no: {Tokens.read_req.go(r) == False{} : Bool}) -> {FT.run(r) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}:
  match r:
    case Wr.Got{t, s}:
      tme.tag(t, s, no)
    case Wr.Bad{}:
      {==}

def Tokens.tokens_ffi_malformed_exact(s, no):
  tme.go(Wr.get_nat(s), no)
