# eukhe: the proof of LAW grep_accounts_every_file

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def ps.add_sr(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ps.add_sr(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# Grep: every entry in one class
# ------------------------------

def ps.sum_mid(pre: List<&2, Nat>, +x: Nat, +post: List<&2, Nat>) -> {Sr.sum(List.append(&2, Nat, pre, (1n+x) <> post)) == 1n+Sr.sum(List.append(&2, Nat, pre, x <> post)) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case +y <> +t:
      +a = Sr.sum(List.append(&2, Nat, t, (1n+x) <> post))
      +b = Sr.sum(List.append(&2, Nat, t, x <> post))
      Equal.trans(Nat, Nat.add(y, a), Nat.add(y, 1n+b), 1n+Nat.add(y, b), Equal.cong(Nat, Nat, z => Nat.add(y, z), a, 1n+b, ps.sum_mid(t, x, post)), ps.add_sr(y, b))

def ps.total_part(pa: Bool, c: Sr.Count) -> {Sr.Count.total(Sr.Count.part(pa, c)) == Sr.Count.total(c) : Nat}:
  match pa:
    case True{}:
      match c:
        case Sr.Count{a, b, d, e, f, g, h, i, j, q}:
          {==}
    case False{}:
      {==}

# one more entry in a class is one more in all
def ps.total_add(c: Sr.Count, x: Sr.Class) -> {Sr.Count.total(Sr.Count.add(c, x)) == 1n+Sr.Count.total(c) : Nat}:
  match c:
    case Sr.Count{+a, +b, +d, +e, +f, +g, +h, +i, +j, q}:
      match x:
        case Sr.NoMatch{}:
          ps.sum_mid([], a, [b, d, e, f, g, h, i, j])
        case Sr.Shown{}:
          ps.sum_mid([a], b, [d, e, f, g, h, i, j])
        case Sr.PagedOut{}:
          ps.sum_mid([a, b], d, [e, f, g, h, i, j])
        case Sr.Unsearched{}:
          ps.sum_mid([a, b, d], e, [f, g, h, i, j])
        case Sr.Skipped{w}:
          match w:
            case Sr.Binary{}:
              ps.sum_mid([a, b, d, e], f, [g, h, i, j])
            case Sr.Unreadable{}:
              ps.sum_mid([a, b, d, e, f], g, [h, i, j])
            case Sr.Excluded{}:
              ps.sum_mid([a, b, d, e, f, g], h, [i, j])
            case Sr.Link{}:
              ps.sum_mid([a, b, d, e, f, g, h], i, [j])
            case Sr.Broken{}:
              ps.sum_mid([a, b, d, e, f, g, h, i], j, [])

def ps.total_account(os: List<&2, Sr.Out>) -> {Sr.Count.total(Sr.account(os)) == List.length(&2, Sr.Out, os) : Nat}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Sr.Out{i, +c, t, +pa}:
          +acc = Sr.account(rest)
          +grown = Sr.Count.add(acc, c)
          Equal.trans(Nat, Sr.Count.total(Sr.Count.part(pa, grown)), Sr.Count.total(grown), 1n+List.length(&2, Sr.Out, rest), ps.total_part(pa, grown), Equal.trans(Nat, Sr.Count.total(grown), 1n+Sr.Count.total(acc), 1n+List.length(&2, Sr.Out, rest), ps.total_add(acc, c), Equal.cong(Nat, Nat, z => 1n+z, Sr.Count.total(acc), List.length(&2, Sr.Out, rest), ps.total_account(rest))))

def ps.len_run(es: List<&2, Sr.Ent>, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> {List.length(&2, Sr.Out, Sr.run(es, p, s, k, rem, n)) == List.length(&2, Sr.Ent, es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      %ps.len_run(rest, p, s, k, Sr.left(e, p, rem), Sr.seen(e, rem, n)) : {1n+List.length(&2, Sr.Out, Sr.run(rest, p, s, k, Sr.left(e, p, rem), Sr.seen(e, rem, n))) == 1n+_ : Nat}
      {==}

# the law grep_accounts_every_file
def ps.accounts_every_file(+es: List<&2, Sr.Ent>, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> {Sr.Count.total(Sr.account(Sr.run(es, p, s, k, rem, n))) == List.length(&2, Sr.Ent, es) : Nat}:
  +os = Sr.run(es, p, s, k, rem, n)
  Equal.trans(Nat, Sr.Count.total(Sr.account(os)), List.length(&2, Sr.Out, os), List.length(&2, Sr.Ent, es), ps.total_account(os), ps.len_run(es, p, s, k, rem, n))

# (F6) What grep searched

def DocSearch.grep_accounts_every_file(es, p, s, k, rem, n):
  ps.accounts_every_file(es, p, s, k, rem, n)
