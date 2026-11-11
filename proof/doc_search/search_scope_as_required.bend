# eukhe: the proof of LAW search_scope_as_required
#
# PROOF: the scope is scope.of(multi, skip, scope.k(lim)); per multi, its
# multi is that multi and its cap and skip are those of that scope; the
# page size is lim + 1, or 20 without a limit, per lim.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def sso.multi(m: Bool, -skip: Nat, -k: Nat) -> {DocSearch.ds_sc_multi(Sr.scope.of(m, skip, k)) == m : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def sso.k(lim: Maybe<&2, Nat>) -> {Sr.scope.k(lim) == DocSearch.ds_page_size(lim) : Nat}:
  match lim:
    case None{}:
      {==}
    case Some{l}:
      {==}

def sso.rest(m: Bool, +skip: Nat, +lim: Maybe<&2, Nat>) -> {DocSearch.ds_sc_rest(Sr.scope.of(m, skip, Sr.scope.k(lim))) == [DocSearch.ds_nat_if(DocSearch.ds_sc_multi(Sr.scope.of(m, skip, Sr.scope.k(lim))), 20n, 200n), DocSearch.ds_nat_if(DocSearch.ds_sc_multi(Sr.scope.of(m, skip, Sr.scope.k(lim))), skip, 0n), DocSearch.ds_page_size(lim)] : List<&2, Nat>}:
  match m:
    case True{}:
      Equal.cong(Nat, List<&2, Nat>, v => [20n, skip, v], Sr.scope.k(lim), DocSearch.ds_page_size(lim), sso.k(lim))
    case False{}:
      Equal.cong(Nat, List<&2, Nat>, v => [200n, 0n, v], Sr.scope.k(lim), DocSearch.ds_page_size(lim), sso.k(lim))

def DocSearch.search_scope_as_required(roots, dirs, skip, lim):
  +m = Bool.or(Nat.is_lt(1n, roots), Nat.is_lt(0n, dirs))
  (sso.multi(m, skip, Sr.scope.k(lim)), sso.rest(m, skip, lim))
