# eukhe: lemmas the proofs of area doc_search share

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ../../laws/wire.bend as Wire

def documents.ps.MD(m: Maybe<&2, Nat>, t: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      t

def documents.ps.none_some(-A: Type, -c: Nat, e: {None{} == Some{c} : Maybe<&2, Nat>}) -> A:
  %e : documents.ps.MD(_, A)
  Unit{}

def ps.some_inj(-a: Nat, -b: Nat, e: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), Some{a}, Some{b}, e)

# Pages
# -----

def ps.take_drop(xs: List<&2, Nat>, k: Nat) -> {List.append(&2, Nat, List.take(&2, Nat, xs, k), List.drop(&2, Nat, xs, k)) == xs : List<&2, Nat>}:
  match xs k:
    case Nil{} k:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      %ps.take_drop(t, p) : {h <> List.append(&2, Nat, List.take(&2, Nat, t, p), List.drop(&2, Nat, t, p)) == h <> _ : List<&2, Nat>}
      {==}

def ps.drop_drop(xs: List<&2, Nat>, s: Nat, +k: Nat) -> {List.drop(&2, Nat, List.drop(&2, Nat, xs, s), k) == List.drop(&2, Nat, xs, Nat.add(s, k)) : List<&2, Nat>}:
  match xs s:
    case Nil{} s:
      match k:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      ps.drop_drop(t, p, k)

def ps.put_c(after: List<&2, Nat>, -c0: Nat, -c: Nat, h: {Sr.next.put(after, c0) == Some{c} : Maybe<&2, Nat>}) -> {c0 == c : Nat}:
  match after:
    case Nil{}:
      documents.ps.none_some({c0 == c : Nat}, c, h)
    case x <> t:
      ps.some_inj(c0, c, h)

# the continuation is S + K
def ps.next_c(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> {Nat.add(s, k) == c : Nat}:
  match k:
    case 0n:
      documents.ps.none_some({Nat.add(s, 0n) == c : Nat}, c, h)
    case 1n+j:
      ps.put_c(List.drop(&2, Nat, ps, Nat.add(s, 1n+j)), Nat.add(s, 1n+j), c, h)

# the page at S + K and what follows it are the list after S
def ps.contig(+ps: List<&2, Nat>, +s: Nat, +k: Nat) -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, Nat.add(s, k), k), List.drop(&2, Nat, List.drop(&2, Nat, ps, Nat.add(s, k)), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  +d = List.drop(&2, Nat, ps, Nat.add(s, k))
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, d, k), List.drop(&2, Nat, d, k)), d, ps.take_drop(d, k)) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  %ps.drop_drop(ps, s, k) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  ps.take_drop(List.drop(&2, Nat, ps, s), k)

# The rules exactly
# -----------------

# the code's sum is the spec's
def ds.sum(xs: List<&2, Nat>) -> {Sr.sum(xs) == DocSearch.ds_sum(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %ds.sum(t) : {Nat.add(x, Sr.sum(t)) == Nat.add(x, _) : Nat}
      {==}

# The entry
# ---------

def dsb.BD(b: Bool, A: Type, B: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      B

# True is not False: anything follows
def dsb.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : dsb.BD(_, Unit, A)
  Unit{}

# a list that fits reads back whole (laws/wire.bend wire_list_round_trip,
# turned around to rewrite a decoded spelling into its list)
def dsb.read(+xs: List<&2, Nat>, h: {DocSearch.ds_fits(xs) == True{} : Bool}) -> {Wr.Got{xs, ""} == Wr.get_list(~Nat, ~Wr.get_nat, DocSearch.ds_spell(xs)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, "")), Wr.Got{xs, ""}, Wire.wire_list_round_trip(xs, "", h))

def dsb.bitn(b: Bool) -> {FDs.bitn(b) == DocSearch.ds_bit(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dsb.maybn(m: Maybe<&2, Nat>) -> {FDs.maybn(m) == DocSearch.ds_opt(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def dsb.bit_of(b: Bool) -> {Some{b} == FDs.bit(DocSearch.ds_bit(b)) : Maybe<&2, Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dsb.why(w: Sr.Reason) -> {FDs.why.n(w) == DocSearch.ds_why(w) : Nat}:
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

def dsb.cls(c: Sr.Class) -> {FDs.cls.n(c) == DocSearch.ds_class(c) : Nat}:
  match c:
    case Sr.NoMatch{}:
      {==}
    case Sr.Shown{}:
      {==}
    case Sr.PagedOut{}:
      {==}
    case Sr.Unsearched{}:
      {==}
    case Sr.Skipped{w}:
      %dsb.why(w) : {4n+FDs.why.n(w) == 4n+_ : Nat}
      {==}

# the reply to what a file held is the spec's
def dsb.said(o: Sr.Out, +k: Nat) -> {FDs.step.met.nats(o, k) == DocSearch.ds_said(o, k) : List<&2, Nat>}:
  match o:
    case Sr.Out{i, +c, +cut, +pa}:
      %dsb.cls(c) : {[FDs.cls.n(c), FDs.bitn(cut), FDs.bitn(pa), k] == [_, DocSearch.ds_bit(cut), DocSearch.ds_bit(pa), k] : List<&2, Nat>}
      %dsb.bitn(cut) : {[FDs.cls.n(c), FDs.bitn(cut), FDs.bitn(pa), k] == [FDs.cls.n(c), _, DocSearch.ds_bit(pa), k] : List<&2, Nat>}
      %dsb.bitn(pa) : {[FDs.cls.n(c), FDs.bitn(cut), FDs.bitn(pa), k] == [FDs.cls.n(c), FDs.bitn(cut), _, k] : List<&2, Nat>}
      {==}

# the event a spelled file reads as
def dsb.met(f: Sr.Form) -> {Some{FDs.Met{f}} == FDs.ev(DocSearch.ds_met(f)) : Maybe<&2, FDs.Ev>}:
  match f:
    case Sr.Opened{h, big}:
      match big:
        case True{}:
          {==}
        case False{}:
          {==}
    case Sr.Skip{w}:
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

# the ranges a spelled ask reads as
def dsb.ranges(rs: List<&2, Sr.Range>) -> {Some{rs} == FDs.ranges(DocSearch.ds_bounds(rs)) : Maybe<&2, List<&2, Sr.Range>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case Sr.Range{+a, z}:
          match z:
            case None{}:
              %dsb.ranges(t) : {Some{Sr.Range{a, None{}} <> t} == FDs.ranges.cons(Sr.Range{a, None{}}, _) : Maybe<&2, List<&2, Sr.Range>>}
              {==}
            case Some{+e}:
              %dsb.ranges(t) : {Some{Sr.Range{a, Some{e}} <> t} == FDs.ranges.cons(Sr.Range{a, Some{e}}, _) : Maybe<&2, List<&2, Sr.Range>>}
              {==}

# Refusals
# --------

# a or False is False only when a is
def dsb.or_f(a: Bool, e: {Bool.or(a, False{}) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

# a Nat over 1 is no Bool
def dsb.bit_none(n: Nat, e: {Nat.is_le(n, 1n) == False{} : Bool}) -> {None{} == FDs.bit(n) : Maybe<&2, Bool>}:
  match n:
    case 0n:
      dsb.tf({None{} == FDs.bit(0n) : Maybe<&2, Bool>}, e)
    case 1n:
      dsb.tf({None{} == FDs.bit(1n) : Maybe<&2, Bool>}, e)
    case 2n+x:
      {==}

# pairs of an odd count read as no ranges
def dsb.ranges_none(xs: List<&2, Nat>, e: {DocSearch.ds_pairs_ok(xs) == False{} : Bool}) -> {None{} == FDs.ranges(xs) : Maybe<&2, List<&2, Sr.Range>>}:
  match xs:
    case Nil{}:
      dsb.tf({None{} == FDs.ranges(Nil{}) : Maybe<&2, List<&2, Sr.Range>>}, e)
    case a <> t:
      match t:
        case Nil{}:
          {==}
        case +z <> u:
          %dsb.ranges_none(u, e) : {None{} == FDs.ranges.cons(Sr.Range{a, FDs.stop(z)}, _) : Maybe<&2, List<&2, Sr.Range>>}
          {==}
