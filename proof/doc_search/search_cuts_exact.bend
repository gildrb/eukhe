# eukhe: the proof of LAW search_cuts_exact: the model and the spec put a
# cut shown entry in, entry by entry

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def sce.why(+i: Nat, w: Sr.Reason, cut: Bool, +r: List<&2, Nat>) -> {Sr.cut.put(i, Sr.Skipped{w}, cut, r) == DocSearch.ds_cut_if(Bool.and(Nat.is_eq(DocSearch.ds_class(Sr.Skipped{w}), 1n), cut), i, r) : List<&2, Nat>}:
  match w:
    case Sr.Binary{}:
      {==}
    case Sr.Unreadable{}:
      {==}
    case Sr.Excluded{}:
      {==}
    case Sr.Link{}:
      {==}
    case Sr.Broken{}:
      {==}

# one entry: put in exactly when it is shown and cut
def sce.put(+i: Nat, c: Sr.Class, +cut: Bool, +r: List<&2, Nat>) -> {Sr.cut.put(i, c, cut, r) == DocSearch.ds_cut_if(Bool.and(Nat.is_eq(DocSearch.ds_class(c), 1n), cut), i, r) : List<&2, Nat>}:
  match c:
    case Sr.NoMatch{}:
      {==}
    case Sr.Shown{}:
      match cut:
        case True{}:
          {==}
        case False{}:
          {==}
    case Sr.PagedOut{}:
      {==}
    case Sr.Unsearched{}:
      {==}
    case Sr.Skipped{w}:
      sce.why(i, w, cut, r)

def DocSearch.search_cuts_exact(os):
  match os:
    case Nil{}:
      {==}
    case o <> t:
      match o:
        case Sr.Out{+i, +c, +cut, pa}:
          %DocSearch.search_cuts_exact(t) : {Sr.cut.put(i, c, cut, Sr.cuts(t)) == DocSearch.ds_cut_if(Bool.and(Nat.is_eq(DocSearch.ds_class(c), 1n), cut), i, _) : List<&2, Nat>}
          sce.put(i, c, cut, Sr.cuts(t))
