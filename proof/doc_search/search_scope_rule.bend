# eukhe: the proof of LAW search_scope_rule: the page size of a limit is the
# spec's, and the scope of either kind is the spec's record

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def rule.k(m: Maybe<&2, Nat>) -> {Sr.scope.k(m) == DocSearch.ds_page_size(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def rule.of(b: Bool, +s: Nat, +k: Nat) -> {Sr.scope.of(b, s, k) == Sr.Scope{b, DocSearch.ds_nat_if(b, 20n, 200n), DocSearch.ds_nat_if(b, s, 0n), k} : Sr.Scope}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def DocSearch.search_scope_rule(roots, dirs, skip, lim):
  +b = Bool.or(Nat.is_lt(1n, roots), Nat.is_lt(0n, dirs))
  %rule.k(lim) : {Sr.scope(roots, dirs, skip, lim) == Sr.Scope{b, DocSearch.ds_nat_if(b, 20n, 200n), DocSearch.ds_nat_if(b, skip, 0n), _} : Sr.Scope}
  rule.of(b, skip, Sr.scope.k(lim))
