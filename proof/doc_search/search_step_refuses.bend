# eukhe: the proof of LAW search_step_refuses: a list of no event's shape reads as no
# event; a list with input left over or no list is no event either

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def stepr.why_none(n: Nat, e: {Nat.is_le(n, 4n) == False{} : Bool}) -> {None{} == FDs.why(n) : Maybe<&2, Sr.Reason>}:
  match n:
    case 0n:
      LADocSearch.dsb.tf({None{} == FDs.why(0n) : Maybe<&2, Sr.Reason>}, e)
    case 1n:
      LADocSearch.dsb.tf({None{} == FDs.why(1n) : Maybe<&2, Sr.Reason>}, e)
    case 2n:
      LADocSearch.dsb.tf({None{} == FDs.why(2n) : Maybe<&2, Sr.Reason>}, e)
    case 3n:
      LADocSearch.dsb.tf({None{} == FDs.why(3n) : Maybe<&2, Sr.Reason>}, e)
    case 4n:
      LADocSearch.dsb.tf({None{} == FDs.why(4n) : Maybe<&2, Sr.Reason>}, e)
    case 5n+x:
      {==}

def stepr.opened(t: List<&2, Nat>, e: {Bool.and(DocSearch.ds_len_is(t, 2n), DocSearch.ds_last_bit(t)) == False{} : Bool}) -> {None{} == FDs.ev.o(t) : Maybe<&2, FDs.Ev>}:
  match t:
    case Nil{}:
      {==}
    case +h <> a:
      match a:
        case Nil{}:
          {==}
        case +b <> c:
          match c:
            case Nil{}:
              %LADocSearch.dsb.bit_none(b, e) : {None{} == FDs.ev.opened(h, _) : Maybe<&2, FDs.Ev>}
              {==}
            case x <> d:
              {==}

def stepr.skipped(t: List<&2, Nat>, e: {Bool.and(DocSearch.ds_len_is(t, 1n), DocSearch.ds_last_why(t)) == False{} : Bool}) -> {None{} == FDs.ev.s(t) : Maybe<&2, FDs.Ev>}:
  match t:
    case Nil{}:
      {==}
    case +w <> a:
      match a:
        case Nil{}:
          %stepr.why_none(w, e) : {None{} == FDs.ev.skip(_) : Maybe<&2, FDs.Ev>}
          {==}
        case x <> b:
          {==}

# a list of no event's shape is no event
def stepr.ev(xs: List<&2, Nat>, e: {DocSearch.ds_event_ok(xs) == False{} : Bool}) -> {None{} == FDs.ev(xs) : Maybe<&2, FDs.Ev>}:
  match xs:
    case Nil{}:
      {==}
    case tag <> +t:
      match tag:
        case 0n:
          %LADocSearch.dsb.ranges_none(t, LADocSearch.dsb.or_f(DocSearch.ds_pairs_ok(t), e)) : {None{} == FDs.ev.ask(_) : Maybe<&2, FDs.Ev>}
          {==}
        case 1n:
          stepr.opened(t, LADocSearch.dsb.or_f(Bool.and(DocSearch.ds_len_is(t, 2n), DocSearch.ds_last_bit(t)), e))
        case 2n:
          stepr.skipped(t, e)
        case 3n+x:
          {==}

def stepr.end(+w: FDs.St, b: Bool, +xs: List<&2, Nat>, e: {DocSearch.ds_event_of(DocSearch.ds_whole.end(b, xs)) == False{} : Bool}) -> {FDs.step.end(w, b, xs) == FDs.step.ev(w, None{}) : FDs.St & String}:
  match b:
    case True{}:
      %stepr.ev(xs, e) : {FDs.step.ev(w, _) == FDs.step.ev(w, None{}) : FDs.St & String}
      {==}
    case False{}:
      {==}

def stepr.got(+w: FDs.St, r: Wr.Dec<List<&2, Nat>>, e: {DocSearch.ds_event_of(DocSearch.ds_whole(r)) == False{} : Bool}) -> {FDs.step.got(w, r) == FDs.step.ev(w, None{}) : FDs.St & String}:
  match r:
    case Wr.Got{xs, rest}:
      stepr.end(w, String.is_empty(rest), xs, e)
    case Wr.Bad{}:
      {==}

def DocSearch.search_step_refuses(p, s, k, rem, n, t, maxb, x, no):
  stepr.got(FDs.Walk{p, s, k, rem, n, t, maxb}, Wr.get_list(~Nat, ~Wr.get_nat, x), no)
