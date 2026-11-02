# eukhe: the proof of LAW search_page_answers: the request reads back whole (the wire's
# list round trip), its multi bit reads back, and the reply's Nats are the
# spec's: the entry works the page out from t (Sr.page.n, next.n,
# past.n), which is the page, continuation and skip past the end over
# the t files upto(t)

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def pg.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %pg.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def pg.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pg.add_succ(p, b))

# the files i, i + 1, ... after the first s of them
def pg.drop(t: Nat, +i: Nat, s: Nat) -> {Sr.upto.go(Nat.sub(t, s), Nat.add(s, i)) == List.drop(&2, Nat, Sr.upto.go(t, i), s) : List<&2, Nat>}:
  match t s:
    case 0n s:
      {==}
    case 1n+u 0n:
      {==}
    case 1n++u 1n++p:
      %pg.add_succ(p, i) : {Sr.upto.go(Nat.sub(u, p), _) == List.drop(&2, Nat, Sr.upto.go(u, 1n+i), p) : List<&2, Nat>}
      pg.drop(u, 1n+i, p)

# the first k of the files i, i + 1, ... (n of them)
def pg.take(n: Nat, +i: Nat, k: Nat) -> {Sr.upto.go(Nat.min(k, n), i) == List.take(&2, Nat, Sr.upto.go(n, i), k) : List<&2, Nat>}:
  match n k:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+u 0n:
      {==}
    case 1n+u 1n+j:
      %pg.take(u, 1n+i, j) : {i <> Sr.upto.go(Nat.min(j, u), 1n+i) == i <> _ : List<&2, Nat>}
      {==}

def pg.put(n: Nat, -x: Nat, -c: Nat) -> {Sr.next.n.put(n, c) == Sr.next.put(Sr.upto.go(n, x), c) : Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+u:
      {==}

def pg.empty(n: Nat, -x: Nat) -> {Nat.is_eq(n, 0n) == List.is_empty(&2, Nat, Sr.upto.go(n, x)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+u:
      {==}

# the files 0 .. t - 1 after the first s, from s on
def pg.from(+t: Nat, +s: Nat) -> {Sr.upto.go(Nat.sub(t, s), s) == List.drop(&2, Nat, Sr.upto(t), s) : List<&2, Nat>}:
  %pg.add_zero(s) : {Sr.upto.go(Nat.sub(t, s), _) == List.drop(&2, Nat, Sr.upto(t), s) : List<&2, Nat>}
  pg.drop(t, 0n, s)

def pg.page(+t: Nat, +s: Nat, +k: Nat) -> {Sr.page.n(t, s, k) == Sr.page(Sr.upto(t), s, k) : List<&2, Nat>}:
  %pg.from(t, s) : {Sr.upto.go(Nat.min(k, Nat.sub(t, s)), s) == List.take(&2, Nat, _, k) : List<&2, Nat>}
  pg.take(Nat.sub(t, s), s, k)

def pg.next(m: Bool, +t: Nat, +s: Nat, k: Nat) -> {Sr.grep.next.n(m, t, s, k) == Sr.grep.next(m, Sr.upto(t), s, k) : Maybe<&2, Nat>}:
  match m:
    case False{}:
      {==}
    case True{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          +c = Nat.add(s, 1n+j)
          %pg.from(t, c) : {Sr.next.n.put(Nat.sub(t, c), c) == Sr.next.put(_, c) : Maybe<&2, Nat>}
          pg.put(Nat.sub(t, c), c, c)

def pg.past(m: Bool, t: Nat, +s: Nat) -> {Sr.grep.past.n(m, t, s) == Sr.grep.past(m, Sr.upto(t), s) : Bool}:
  match m:
    case False{}:
      {==}
    case True{}:
      match t:
        case 0n:
          {==}
        case 1n++u:
          %pg.from(1n+u, s) : {Nat.is_eq(Nat.sub(1n+u, s), 0n) == List.is_empty(&2, Nat, _) : Bool}
          pg.empty(Nat.sub(1n+u, s), s)

def page.reply(+m: Bool, +t: Nat, +s: Nat, +k: Nat) -> {FDs.answer.page(t, s, k, m) == DocSearch.ds_opt(Sr.grep.next(m, Sr.upto(t), s, k)) <> DocSearch.ds_bit(Sr.grep.past(m, Sr.upto(t), s)) <> Sr.page(Sr.upto(t), s, k) : List<&2, Nat>}:
  +x = Sr.grep.next.n(m, t, s, k)
  +y = Sr.grep.past.n(m, t, s)
  +z = Sr.page.n(t, s, k)
  %pg.next(m, t, s, k) : {FDs.answer.page(t, s, k, m) == DocSearch.ds_opt(_) <> DocSearch.ds_bit(Sr.grep.past(m, Sr.upto(t), s)) <> Sr.page(Sr.upto(t), s, k) : List<&2, Nat>}
  %pg.past(m, t, s) : {FDs.answer.page(t, s, k, m) == DocSearch.ds_opt(x) <> DocSearch.ds_bit(_) <> Sr.page(Sr.upto(t), s, k) : List<&2, Nat>}
  %pg.page(t, s, k) : {FDs.answer.page(t, s, k, m) == DocSearch.ds_opt(x) <> DocSearch.ds_bit(y) <> _ : List<&2, Nat>}
  %LADocSearch.dsb.maybn(x) : {FDs.maybn(x) <> FDs.bitn(y) <> z == _ <> DocSearch.ds_bit(y) <> z : List<&2, Nat>}
  %LADocSearch.dsb.bitn(y) : {FDs.maybn(x) <> FDs.bitn(y) <> z == FDs.maybn(x) <> _ <> z : List<&2, Nat>}
  {==}

def DocSearch.search_page_answers(t, s, k, m, h):
  +xs = {[0n, t, s, k, DocSearch.ds_bit(m)] : List<&2, Nat>}
  +ans = {DocSearch.ds_opt(Sr.grep.next(m, Sr.upto(t), s, k)) <> DocSearch.ds_bit(Sr.grep.past(m, Sr.upto(t), s)) <> Sr.page(Sr.upto(t), s, k) : List<&2, Nat>}
  %LADocSearch.dsb.read(xs, h) : {FDs.ffi.got(_) == DocSearch.ds_spell(ans) : String}
  %LADocSearch.dsb.bit_of(m) : {FDs.ffi.ask(FDs.req.page(t, s, k, _)) == DocSearch.ds_spell(ans) : String}
  Equal.cong(List<&2, Nat>, String, x => Wr.put_list(~Nat, ~Wr.put_nat, x, ""), FDs.answer.page(t, s, k, m), ans, page.reply(m, t, s, k))
