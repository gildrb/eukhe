# eukhe: the proof of LAW search_open_refuses: a list of another length than six is no
# limits; input left over or no list refuses too

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def openr.lims(xs: List<&2, Nat>, e: {DocSearch.ds_len_is(xs, 6n) == False{} : Bool}) -> {None{} == FDs.lims(xs) : Maybe<&2, FDs.St>}:
  match xs:
    case Nil{}:
      {==}
    case p <> a:
      match a:
        case Nil{}:
          {==}
        case s <> b:
          match b:
            case Nil{}:
              {==}
            case k <> c:
              match c:
                case Nil{}:
                  {==}
                case rem <> d:
                  match d:
                    case Nil{}:
                      {==}
                    case t <> g:
                      match g:
                        case Nil{}:
                          {==}
                        case maxb <> f:
                          match f:
                            case Nil{}:
                              LADocSearch.dsb.tf({None{} == FDs.lims([p, s, k, rem, t, maxb]) : Maybe<&2, FDs.St>}, e)
                            case x <> y:
                              {==}

def openr.end(b: Bool, +xs: List<&2, Nat>, e: {DocSearch.ds_open_of(DocSearch.ds_whole.end(b, xs)) == False{} : Bool}) -> {FDs.open.end(b, xs) == (FDs.Shut{}, Wr.err("doc_search: malformed open")) : FDs.St & String}:
  match b:
    case True{}:
      %openr.lims(xs, e) : {FDs.open.of(_) == (FDs.Shut{}, Wr.err("doc_search: malformed open")) : FDs.St & String}
      {==}
    case False{}:
      {==}

def openr.got(r: Wr.Dec<List<&2, Nat>>, e: {DocSearch.ds_open_of(DocSearch.ds_whole(r)) == False{} : Bool}) -> {FDs.open.got(r) == (FDs.Shut{}, Wr.err("doc_search: malformed open")) : FDs.St & String}:
  match r:
    case Wr.Got{xs, rest}:
      openr.end(String.is_empty(rest), xs, e)
    case Wr.Bad{}:
      {==}

def DocSearch.search_open_refuses(s, no):
  openr.got(Wr.get_list(~Nat, ~Wr.get_nat, s), no)
