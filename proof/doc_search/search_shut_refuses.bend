# eukhe: the proof of LAW search_shut_refuses: the refused state answers before it reads
# the event

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def shut.end(b: Bool, xs: List<&2, Nat>) -> {FDs.step.end(FDs.Shut{}, b, xs) == (FDs.Shut{}, Wr.err("doc_search: the open was refused")) : FDs.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shut.got(r: Wr.Dec<List<&2, Nat>>) -> {FDs.step.got(FDs.Shut{}, r) == (FDs.Shut{}, Wr.err("doc_search: the open was refused")) : FDs.St & String}:
  match r:
    case Wr.Got{xs, rest}:
      shut.end(Wr.end(rest), xs)
    case Wr.Bad{}:
      {==}

def DocSearch.search_shut_refuses(s):
  shut.got(Wr.get_list(~Nat, ~Wr.get_nat, s))
