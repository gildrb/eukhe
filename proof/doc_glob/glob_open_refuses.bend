# eukhe: the proof of LAW glob_open_refuses: an open that is not exactly a skip
# and a limit (0, or 1 and the limit), nothing after, opens the refused state

import Base
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/doc_glob.bend as DocGlob

def gor.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def gor.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : gor.BD(_, G)
  Unit{}

# input left over refuses the limit
def gor.end(+s: Nat, b: Bool, m: Maybe<&2, Nat>, e: {b == False{} : Bool}) -> {FGb.open.lim(s, FGb.lim.end(b, m)) == (FGb.Shut{}, Wr.err("doc_glob: malformed open")) : FGb.St & String}:
  match b:
    case True{}:
      gor.absurd({FGb.open.lim(s, FGb.lim.end(True{}, m)) == (FGb.Shut{}, Wr.err("doc_glob: malformed open")) : FGb.St & String}, e)
    case False{}:
      {==}

def gor.one(+s: Nat, d: Wr.Dec<Nat>, e: {DocGlob.glob.end(d) == False{} : Bool}) -> {FGb.open.lim(s, FGb.lim.one(d)) == (FGb.Shut{}, Wr.err("doc_glob: malformed open")) : FGb.St & String}:
  match d:
    case Wr.Got{l, r}:
      gor.end(s, Wr.end(r), Some{l}, e)
    case Wr.Bad{}:
      {==}

# the limit's tag: 0 then nothing, or 1 then the limit then nothing
def gor.tag(+s: Nat, d: Wr.Dec<Nat>, e: {DocGlob.glob.OpenLim(d) == False{} : Bool}) -> {FGb.open.lim(s, FGb.lim.tag(d)) == (FGb.Shut{}, Wr.err("doc_glob: malformed open")) : FGb.St & String}:
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          gor.end(s, Wr.end(r), None{}, e)
        case 1n:
          gor.one(s, Wr.get_nat(r), e)
        case 2n+x:
          {==}
    case Wr.Bad{}:
      {==}

def gor.got(d: Wr.Dec<Nat>, e: {DocGlob.glob.OpenOk.of(d) == False{} : Bool}) -> {FGb.open.got(d) == (FGb.Shut{}, Wr.err("doc_glob: malformed open")) : FGb.St & String}:
  match d:
    case Wr.Got{s, r}:
      gor.tag(s, Wr.get_nat(r), e)
    case Wr.Bad{}:
      {==}

def DocGlob.glob_open_refuses(x, no):
  gor.got(Wr.get_nat(x), no)
