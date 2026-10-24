# eukhe: the proof of LAW search_scope_answers: the request reads back whole (the wire's
# list round trip), its limit reads back, and the scope's Nats are the
# spec's for either scope

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

# a spelled limit reads back
def scope.stop(m: Maybe<&2, Nat>) -> {m == FDs.stop(DocSearch.ds_opt(m)) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def scope.k(m: Maybe<&2, Nat>) -> {Sr.scope.k(m) == DocSearch.ds_page_size(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def scope.of(b: Bool, +s: Nat, +k: Nat) -> {FDs.answer.scope(Sr.scope.of(b, s, k)) == [DocSearch.ds_bit(b), DocSearch.ds_nat_if(b, 20n, 200n), DocSearch.ds_nat_if(b, s, 0n), k] : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the scope's Nats are the spec's
def scope.all(+r: Nat, +d: Nat, +s: Nat, +l: Maybe<&2, Nat>) -> {FDs.answer.scope(Sr.scope(r, d, s, l)) == DocSearch.ds_scope(r, d, s, l) : List<&2, Nat>}:
  +b = Bool.or(Nat.is_lt(1n, r), Nat.is_lt(0n, d))
  %scope.k(l) : {FDs.answer.scope(Sr.scope(r, d, s, l)) == [DocSearch.ds_bit(b), DocSearch.ds_nat_if(b, 20n, 200n), DocSearch.ds_nat_if(b, s, 0n), _] : List<&2, Nat>}
  scope.of(b, s, Sr.scope.k(l))

def DocSearch.search_scope_answers(roots, dirs, skip, lim, h):
  +xs = {[2n, roots, dirs, skip, DocSearch.ds_opt(lim)] : List<&2, Nat>}
  +ans = DocSearch.ds_scope(roots, dirs, skip, lim)
  %LADocSearch.dsb.read(xs, h) : {FDs.ffi.got(_) == DocSearch.ds_spell(ans) : String}
  %scope.stop(lim) : {FDs.ffi.ask(Some{FDs.ScopeQ{roots, dirs, skip, _}}) == DocSearch.ds_spell(ans) : String}
  Equal.cong(List<&2, Nat>, String, x => Wr.put_list(~Nat, ~Wr.put_nat, x, ""), FDs.answer.scope(Sr.scope(roots, dirs, skip, lim)), ans, scope.all(roots, dirs, skip, lim))
