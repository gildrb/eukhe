# eukhe: the proof of LAW search_list_tests_exact: the model's tests and the specs step
# alike, item by item

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def slt.mem(+x: Nat, xs: List<&2, Nat>) -> {Sr.mem(x, xs) == DocSearch.ds_mem(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> t:
      %slt.mem(x, t) : {Bool.or(Nat.is_eq(y, x), Sr.mem(x, t)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def slt.nodup(xs: List<&2, Nat>) -> {Sr.nodup(xs) == DocSearch.ds_nodup(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      %slt.mem(y, t) : {Bool.and(Bool.not(Sr.mem(y, t)), Sr.nodup(t)) == Bool.and(Bool.not(_), DocSearch.ds_nodup(t)) : Bool}
      %slt.nodup(t) : {Bool.and(Bool.not(Sr.mem(y, t)), Sr.nodup(t)) == Bool.and(Bool.not(Sr.mem(y, t)), _) : Bool}
      {==}

def DocSearch.search_list_tests_exact(x, xs):
  (slt.mem(x, xs), slt.nodup(xs))
