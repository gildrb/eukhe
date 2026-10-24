# eukhe: the proof of LAW search_ffi_refuses: a list of no call's shape reads as no
# call; input left over or no list refuses too

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def ffir.page(t: List<&2, Nat>, e: {Bool.and(DocSearch.ds_len_is(t, 4n), DocSearch.ds_last_bit(t)) == False{} : Bool}) -> {None{} == FDs.req.p(t) : Maybe<&2, FDs.Req>}:
  match t:
    case Nil{}:
      {==}
    case +a <> b:
      match b:
        case Nil{}:
          {==}
        case +s <> c:
          match c:
            case Nil{}:
              {==}
            case +k <> d:
              match d:
                case Nil{}:
                  {==}
                case +m <> g:
                  match g:
                    case Nil{}:
                      %LADocSearch.dsb.bit_none(m, e) : {None{} == FDs.req.page(a, s, k, _) : Maybe<&2, FDs.Req>}
                      {==}
                    case x <> y:
                      {==}

def ffir.limit(t: List<&2, Nat>, e: {Nat.is_lt(0n, List.length(&2, Nat, t)) == False{} : Bool}) -> {None{} == FDs.req.l(t) : Maybe<&2, FDs.Req>}:
  match t:
    case Nil{}:
      {==}
    case l <> cs:
      LADocSearch.dsb.tf({None{} == FDs.req.l(l <> cs) : Maybe<&2, FDs.Req>}, e)

def ffir.scope(t: List<&2, Nat>, e: {DocSearch.ds_len_is(t, 4n) == False{} : Bool}) -> {None{} == FDs.req.c(t) : Maybe<&2, FDs.Req>}:
  match t:
    case Nil{}:
      {==}
    case r <> a:
      match a:
        case Nil{}:
          {==}
        case d <> b:
          match b:
            case Nil{}:
              {==}
            case s <> c:
              match c:
                case Nil{}:
                  {==}
                case l <> g:
                  match g:
                    case Nil{}:
                      LADocSearch.dsb.tf({None{} == FDs.req.c([r, d, s, l]) : Maybe<&2, FDs.Req>}, e)
                    case x <> y:
                      {==}

# a list of no call's shape is no call
def ffir.req(xs: List<&2, Nat>, e: {DocSearch.ds_call_ok(xs) == False{} : Bool}) -> {None{} == FDs.req(xs) : Maybe<&2, FDs.Req>}:
  match xs:
    case Nil{}:
      {==}
    case tag <> +t:
      match tag:
        case 0n:
          ffir.page(t, LADocSearch.dsb.or_f(Bool.and(DocSearch.ds_len_is(t, 4n), DocSearch.ds_last_bit(t)), e))
        case 1n:
          ffir.limit(t, LADocSearch.dsb.or_f(Nat.is_lt(0n, List.length(&2, Nat, t)), e))
        case 2n:
          ffir.scope(t, e)
        case 3n+x:
          {==}

def ffir.end(b: Bool, +xs: List<&2, Nat>, e: {DocSearch.ds_call_of(DocSearch.ds_whole.end(b, xs)) == False{} : Bool}) -> {FDs.ffi.end(b, xs) == Wr.err("doc_search: malformed request") : String}:
  match b:
    case True{}:
      %ffir.req(xs, e) : {FDs.ffi.ask(_) == Wr.err("doc_search: malformed request") : String}
      {==}
    case False{}:
      {==}

def ffir.got(r: Wr.Dec<List<&2, Nat>>, e: {DocSearch.ds_call_of(DocSearch.ds_whole(r)) == False{} : Bool}) -> {FDs.ffi.got(r) == Wr.err("doc_search: malformed request") : String}:
  match r:
    case Wr.Got{xs, rest}:
      ffir.end(String.is_empty(rest), xs, e)
    case Wr.Bad{}:
      {==}

def DocSearch.search_ffi_refuses(s, no):
  ffir.got(Wr.get_list(~Nat, ~Wr.get_nat, s), no)
