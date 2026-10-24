# eukhe: the proof of LAW bound_open_refuses: a list of no open's shape opens the refused state; input left over or no list too

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def orf.three(+b: Nat, +l: Nat, t: Nat, e: {Bound.bd_open_ok([b, l, t]) == False{} : Bool}) -> {FBd.open.of(FBd.cap.lead([b, l, t])) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}:
  match t:
    case 0n:
      LBound.bnd.tf({FBd.open.of(FBd.cap.lead([b, l, 0n])) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}, e)
    case 1n:
      LBound.bnd.tf({FBd.open.of(FBd.cap.lead([b, l, 1n])) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}, e)
    case 2n+y:
      {==}

def orf.more(+b: Nat, +l: Nat, t: Nat, +y: Nat, +w: List<&2, Nat>) -> {FBd.open.of(FBd.cap.lead(b <> l <> t <> y <> w)) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+v:
      {==}

def orf.of(xs: List<&2, Nat>, e: {Bound.bd_open_ok(xs) == False{} : Bool}) -> {FBd.open.of(FBd.cap.lead(xs)) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}:
  match xs:
    case Nil{}:
      {==}
    case +b <> +r:
      match r:
        case Nil{}:
          {==}
        case +l <> +q:
          match q:
            case Nil{}:
              {==}
            case +t <> +z:
              match z:
                case Nil{}:
                  orf.three(b, l, t, e)
                case +y <> +w:
                  orf.more(b, l, t, y, w)

def orf.end(b: Bool, +xs: List<&2, Nat>, e: {Bound.bd_open_of(Bound.bd_whole.end(b, xs)) == False{} : Bool}) -> {FBd.open.end(b, xs) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}:
  match b:
    case True{}:
      orf.of(xs, e)
    case False{}:
      {==}

def orf.got(r: Wr.Dec<List<&2, Nat>>, e: {Bound.bd_open_of(Bound.bd_whole(r)) == False{} : Bool}) -> {FBd.open.got(r) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}:
  match r:
    case Wr.Got{+xs, +rest}:
      orf.end(String.is_empty(rest), xs, e)
    case Wr.Bad{}:
      {==}

def Bound.bound_open_refuses(s, no):
  orf.got(Wr.get_list(~Nat, ~Wr.get_nat, s), no)
