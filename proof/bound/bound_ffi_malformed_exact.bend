# eukhe: the proof of LAW bound_ffi_malformed_exact: a list of no call's shape reads as no call; input left over or no list refuses too

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def mr.notice3(a: Nat, +d: Nat, +s: Nat, e: {Bound.bd_notice_ok([a, d, s]) == False{} : Bool}) -> {None{} == FBd.req.notice([a, d, s]) : Maybe<&2, FBd.Req>}:
  match a:
    case 0n:
      %LBound.bnd.bit_none(s, e) : {None{} == FBd.req.notice.of(Some{False{}}, d, _) : Maybe<&2, FBd.Req>}
      {==}
    case 1n:
      %LBound.bnd.bit_none(s, e) : {None{} == FBd.req.notice.of(Some{True{}}, d, _) : Maybe<&2, FBd.Req>}
      {==}
    case 2n+y:
      {==}

def mr.notice(t: List<&2, Nat>, e: {Bound.bd_notice_ok(t) == False{} : Bool}) -> {None{} == FBd.req.notice(t) : Maybe<&2, FBd.Req>}:
  match t:
    case Nil{}:
      {==}
    case +a <> +r:
      match r:
        case Nil{}:
          {==}
        case +d <> +q:
          match q:
            case Nil{}:
              {==}
            case +s <> +z:
              match z:
                case Nil{}:
                  mr.notice3(a, d, s, e)
                case +y <> +w:
                  {==}

def mr.slice4(+b: Nat, +l: Nat, tl: Nat, +rest: List<&2, Nat>, e: {Bound.bd_cap_body_ok(b <> l <> tl <> rest) == False{} : Bool}) -> {None{} == FBd.req.slice(FBd.cap.lead(b <> l <> tl <> rest)) : Maybe<&2, FBd.Req>}:
  match tl:
    case 0n:
      %LBound.bnd.body_none(rest, e) : {None{} == FBd.req.slice.body(Bd.Cap{b, l, False{}}, _) : Maybe<&2, FBd.Req>}
      {==}
    case 1n:
      %LBound.bnd.body_none(rest, e) : {None{} == FBd.req.slice.body(Bd.Cap{b, l, True{}}, _) : Maybe<&2, FBd.Req>}
      {==}
    case 2n+y:
      {==}

def mr.slice(t: List<&2, Nat>, e: {Bound.bd_cap_body_ok(t) == False{} : Bool}) -> {None{} == FBd.req.slice(FBd.cap.lead(t)) : Maybe<&2, FBd.Req>}:
  match t:
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
            case +tl <> +rest:
              mr.slice4(b, l, tl, rest, e)

# a list of no call's shape is no call
def mr.req(xs: List<&2, Nat>, e: {Bound.bd_call_ok(xs) == False{} : Bool}) -> {None{} == FBd.req(xs) : Maybe<&2, FBd.Req>}:
  match xs:
    case Nil{}:
      {==}
    case +tag <> +t:
      match tag:
        case 0n:
          mr.slice(t, LBound.bnd.or_f(Bound.bd_cap_body_ok(t), e))
        case 1n:
          mr.notice(t, e)
        case 2n+x:
          {==}

def mr.end(b: Bool, +xs: List<&2, Nat>, e: {Bound.bd_call_of(Bound.bd_whole.end(b, xs)) == False{} : Bool}) -> {FBd.ffi.end(b, xs) == Wr.err("bound: malformed request") : String}:
  match b:
    case True{}:
      %mr.req(xs, e) : {FBd.ffi.ask(_) == Wr.err("bound: malformed request") : String}
      {==}
    case False{}:
      {==}

def mr.got(r: Wr.Dec<List<&2, Nat>>, e: {Bound.bd_call_of(Bound.bd_whole(r)) == False{} : Bool}) -> {FBd.ffi.got(r) == Wr.err("bound: malformed request") : String}:
  match r:
    case Wr.Got{+xs, +rest}:
      mr.end(String.is_empty(rest), xs, e)
    case Wr.Bad{}:
      {==}

def Bound.bound_ffi_malformed_exact(s, no):
  mr.got(Wr.get_list(~Nat, ~Wr.get_nat, s), no)
