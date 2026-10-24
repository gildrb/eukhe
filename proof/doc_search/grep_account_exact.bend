# eukhe: the proof of LAW grep_account_exact: one entry adds one to the counter of its
# class (and to the partial count when searched in part), as the spec's
# counts do; by induction on the result

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def gae.part(pa: Bool, +a: Nat, +b: Nat, +d: Nat, +e: Nat, +f: Nat, +g: Nat, +h: Nat, +i: Nat, +j: Nat, +p: Nat) -> {Sr.Count.part(pa, Sr.Count{a, b, d, e, f, g, h, i, j, p}) == Sr.Count{a, b, d, e, f, g, h, i, j, Nat.add(DocSearch.ds_bit(pa), p)} : Sr.Count}:
  match pa:
    case True{}:
      {==}
    case False{}:
      {==}

def gae.step(c: Sr.Class, pa: Bool, +a: Nat, +b: Nat, +d: Nat, +e: Nat, +f: Nat, +g: Nat, +h: Nat, +i: Nat, +j: Nat, +p: Nat) -> {Sr.Count.part(pa, Sr.Count.add(Sr.Count{a, b, d, e, f, g, h, i, j, p}, c)) == Sr.Count{Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 0n)), a), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 1n)), b), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 2n)), d), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 3n)), e), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 4n)), f), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 5n)), g), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 6n)), h), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 7n)), i), Nat.add(DocSearch.ds_bit(Nat.is_eq(DocSearch.ds_class(c), 8n)), j), Nat.add(DocSearch.ds_bit(pa), p)} : Sr.Count}:
  match c:
    case Sr.NoMatch{}:
      gae.part(pa, 1n+a, b, d, e, f, g, h, i, j, p)
    case Sr.Shown{}:
      gae.part(pa, a, 1n+b, d, e, f, g, h, i, j, p)
    case Sr.PagedOut{}:
      gae.part(pa, a, b, 1n+d, e, f, g, h, i, j, p)
    case Sr.Unsearched{}:
      gae.part(pa, a, b, d, 1n+e, f, g, h, i, j, p)
    case Sr.Skipped{w}:
      match w:
        case Sr.Binary{}:
          gae.part(pa, a, b, d, e, 1n+f, g, h, i, j, p)
        case Sr.Unreadable{}:
          gae.part(pa, a, b, d, e, f, 1n+g, h, i, j, p)
        case Sr.Excluded{}:
          gae.part(pa, a, b, d, e, f, g, 1n+h, i, j, p)
        case Sr.Link{}:
          gae.part(pa, a, b, d, e, f, g, h, 1n+i, j, p)
        case Sr.Broken{}:
          gae.part(pa, a, b, d, e, f, g, h, i, 1n+j, p)

def gae.go(os: List<&2, Sr.Out>) -> {Sr.account(os) == Sr.Count{DocSearch.ds_n(os, 0n), DocSearch.ds_n(os, 1n), DocSearch.ds_n(os, 2n), DocSearch.ds_n(os, 3n), DocSearch.ds_n(os, 4n), DocSearch.ds_n(os, 5n), DocSearch.ds_n(os, 6n), DocSearch.ds_n(os, 7n), DocSearch.ds_n(os, 8n), DocSearch.ds_partials(os)} : Sr.Count}:
  match os:
    case Nil{}:
      {==}
    case o <> +t:
      match o:
        case Sr.Out{x, +c, cut, +pa}:
          +sp = {Sr.Count{DocSearch.ds_n(t, 0n), DocSearch.ds_n(t, 1n), DocSearch.ds_n(t, 2n), DocSearch.ds_n(t, 3n), DocSearch.ds_n(t, 4n), DocSearch.ds_n(t, 5n), DocSearch.ds_n(t, 6n), DocSearch.ds_n(t, 7n), DocSearch.ds_n(t, 8n), DocSearch.ds_partials(t)} : Sr.Count}
          +ih = Equal.cong(Sr.Count, Sr.Count, v => Sr.Count.part(pa, Sr.Count.add(v, c)), Sr.account(t), sp, gae.go(t))
          +os = {Sr.Out{x, c, cut, pa} <> t : List<&2, Sr.Out>}
          Equal.trans(Sr.Count, Sr.Count.part(pa, Sr.Count.add(Sr.account(t), c)), Sr.Count.part(pa, Sr.Count.add(sp, c)), Sr.Count{DocSearch.ds_n(os, 0n), DocSearch.ds_n(os, 1n), DocSearch.ds_n(os, 2n), DocSearch.ds_n(os, 3n), DocSearch.ds_n(os, 4n), DocSearch.ds_n(os, 5n), DocSearch.ds_n(os, 6n), DocSearch.ds_n(os, 7n), DocSearch.ds_n(os, 8n), DocSearch.ds_partials(os)}, ih, gae.step(c, pa, DocSearch.ds_n(t, 0n), DocSearch.ds_n(t, 1n), DocSearch.ds_n(t, 2n), DocSearch.ds_n(t, 3n), DocSearch.ds_n(t, 4n), DocSearch.ds_n(t, 5n), DocSearch.ds_n(t, 6n), DocSearch.ds_n(t, 7n), DocSearch.ds_n(t, 8n), DocSearch.ds_partials(t)))

def DocSearch.grep_account_exact(os):
  gae.go(os)
