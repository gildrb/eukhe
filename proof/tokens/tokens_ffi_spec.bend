# eukhe: the proof of LAW tokens_ffi_spec
# The entry and the spec read the same tag and end (one case per stage);
# on the one request both answer the tables (tokens_ffi_blocks: the
# entry's answer to "0," is spell_blocks), on any other input the error.

import Base
import ../../bend/ffi_tokens.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/tokens.bend as Tokens

def tsp.end(b: Bool) -> {FT.run.end(b) == Tokens.spec_entry.of(b) : String}:
  match b:
    case True{}:
      Tokens.tokens_ffi_blocks()
    case False{}:
      {==}

def tsp.tag(t: Nat, +s: String) -> {FT.run.tag(t, s) == Tokens.spec_entry.of(Tokens.read_req.tag(t, s)) : String}:
  match t:
    case 0n:
      tsp.end(Wr.end(s))
    case 1n+p:
      {==}

def tsp.go(r: Wr.Dec<Nat>) -> {FT.run(r) == Tokens.spec_entry.of(Tokens.read_req.go(r)) : String}:
  match r:
    case Wr.Got{t, s}:
      tsp.tag(t, s)
    case Wr.Bad{}:
      {==}

def Tokens.tokens_ffi_spec(s):
  tsp.go(Wr.get_nat(s))
