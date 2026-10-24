# eukhe: the proof of LAW glob_step_refuses: a text that is not exactly a time, a
# path whole or the page, nothing after, reads as no event; no event keeps the
# glob and answers the error form

import Base
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/doc_glob.bend as DocGlob

def gsr.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def gsr.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : gsr.BD(_, G)
  Unit{}

# input left over is no event
def gsr.end(b: Bool, v: FGb.Ev, e: {b == False{} : Bool}) -> {None{} == FGb.ev.end(b, v) : Maybe<&2, FGb.Ev>}:
  match b:
    case True{}:
      gsr.absurd({None{} == FGb.ev.end(True{}, v) : Maybe<&2, FGb.Ev>}, e)
    case False{}:
      {==}

def gsr.met(d: Wr.Dec<Nat>, e: {DocGlob.glob.end(d) == False{} : Bool}) -> {None{} == FGb.ev.met(d) : Maybe<&2, FGb.Ev>}:
  match d:
    case Wr.Got{m, r}:
      gsr.end(Wr.end(r), FGb.Met{m}, e)
    case Wr.Bad{}:
      {==}

def gsr.path(m: Nat, d: Wr.Dec<String>, e: {DocGlob.glob.end_str(d) == False{} : Bool}) -> {None{} == FGb.ev.path(m, d) : Maybe<&2, FGb.Ev>}:
  match d:
    case Wr.Got{p, r}:
      gsr.end(Wr.end(r), FGb.Add{m, p}, e)
    case Wr.Bad{}:
      {==}

def gsr.add(d: Wr.Dec<Nat>, e: {DocGlob.glob.AddOk(d) == False{} : Bool}) -> {None{} == FGb.ev.add(d) : Maybe<&2, FGb.Ev>}:
  match d:
    case Wr.Got{m, r}:
      gsr.path(m, Wr.get_str(r), e)
    case Wr.Bad{}:
      {==}

# a text of no event's shape is no event
def gsr.ev(d: Wr.Dec<Nat>, e: {DocGlob.glob.EvOk.of(d) == False{} : Bool}) -> {None{} == FGb.ev(d) : Maybe<&2, FGb.Ev>}:
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          gsr.met(Wr.get_nat(r), e)
        case 1n:
          gsr.add(Wr.get_nat(r), e)
        case 2n:
          gsr.end(Wr.end(r), FGb.Show{}, e)
        case 3n+x:
          {==}
    case Wr.Bad{}:
      {==}

def DocGlob.glob_step_refuses(s, k, c, len, low, xs, x, no):
  %gsr.ev(Wr.get_nat(x), no) : {FGb.step.ev(FGb.Gl{s, k, c, len, low, xs}, _) == (FGb.Gl{s, k, c, len, low, xs}, Wr.err("doc_glob: malformed event")) : FGb.St & String}
  {==}
