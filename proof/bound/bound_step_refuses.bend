# eukhe: the proof of LAW bound_step_refuses: a list of no event's shape reads as no event; input left over or no list is no event either

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def sr.three(+tag: Nat, t: List<&2, Nat>, e: {Bool.and(Bound.bd_len_is(t, 3n), Bound.bd_third_bit(t)) == False{} : Bool}) -> {None{} == FBd.ev.three(tag, t) : Maybe<&2, FBd.Ev>}:
  match t:
    case Nil{}:
      {==}
    case +n <> +a:
      match a:
        case Nil{}:
          {==}
        case +k <> +b:
          match b:
            case Nil{}:
              {==}
            case +o <> +c:
              match c:
                case Nil{}:
                  %LBound.bnd.bit_none(o, e) : {None{} == FBd.ev.counts(_, tag, n, k) : Maybe<&2, FBd.Ev>}
                  {==}
                case +x <> +y:
                  {==}

# a list of no event's shape is no event
def sr.ev(xs: List<&2, Nat>, e: {Bound.bd_event_ok(xs) == False{} : Bool}) -> {None{} == FBd.ev(xs) : Maybe<&2, FBd.Ev>}:
  match xs:
    case Nil{}:
      {==}
    case +tag <> +t:
      match tag:
        case 0n:
          sr.three(0n, t, LBound.bnd.or_f(Bool.and(Bound.bd_len_is(t, 3n), Bound.bd_third_bit(t)), e))
        case 1n:
          sr.three(1n, t, LBound.bnd.or_f(Bool.and(Bound.bd_len_is(t, 3n), Bound.bd_third_bit(t)), e))
        case 2n:
          %LBound.bnd.body_none(t, e) : {None{} == FBd.ev.look(_) : Maybe<&2, FBd.Ev>}
          {==}
        case 3n+x:
          {==}

def sr.end(+w: FBd.St, b: Bool, +xs: List<&2, Nat>, e: {Bound.bd_event_of(Bound.bd_whole.end(b, xs)) == False{} : Bool}) -> {FBd.step.end(w, b, xs) == FBd.step.ev(w, None{}) : FBd.St & String}:
  match b:
    case True{}:
      %sr.ev(xs, e) : {FBd.step.ev(w, _) == FBd.step.ev(w, None{}) : FBd.St & String}
      {==}
    case False{}:
      {==}

def sr.got(+w: FBd.St, r: Wr.Dec<List<&2, Nat>>, e: {Bound.bd_event_of(Bound.bd_whole(r)) == False{} : Bool}) -> {FBd.step.got(w, r) == FBd.step.ev(w, None{}) : FBd.St & String}:
  match r:
    case Wr.Got{+xs, +rest}:
      sr.end(w, String.is_empty(rest), xs, e)
    case Wr.Bad{}:
      {==}

def Bound.bound_step_refuses(s, x, no):
  sr.got(FBd.Run{s}, Wr.get_list(~Nat, ~Wr.get_nat, x), no)
