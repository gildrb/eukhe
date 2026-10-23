# eukhe: lemmas the proofs of area sandbox share

import Base
import ../../bend/sandbox.bend as Sb
import ../../LAWS.bend as Laws

# ---- sandbox ----

# proof_sandbox: the S3 laws (docs/runtime.md) of the sandbox model in
# bend/sandbox.bend: the protocol and the copy-on-write hand-back.
#
# The protocol: one host step adds one reply and runs the frame iff it is
# accepted (`px.ids_add`, `px.ok_add`, `px.len_add`); each law follows by
# induction on the frames. The hand-back: the lookup of a path k in the new
# workspace is the merge of k when k is listed, else nothing
# (`px.read_back`), and k is a conflict iff it is listed and its merge
# clashes (`px.cl_back`). The merge of one path then decides each law
# (`px.keep_body`, `px.take_body`, `px.clash_one`, `px.real`).

# Logic
# -----

def px.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def px.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : px.BD(_, A, Unit)
  Unit{}

def px.and_false(b: Bool) -> {False{} == Bool.and(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Numbers
# -------

def px.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      px.eq_refl(p)

def px.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      px.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      px.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, px.eq_true(p, q, h))

# 2. A copy-on-write workspace
# ----------------------------

# the merge of path k
def px.mk(+par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat) -> Sb.One:
  Sb.merge1(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k))

def px.sel(b: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      m
    case False{}:
      None{}

def px.sel_none(b: Bool) -> {None{} == px.sel(b, None{}) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a file added at k is what k reads, else what follows
def px.read_hit(+k: Nat, m: Maybe<&2, Nat>, +W: List<&2, Sb.Doc>, +b: Bool, ih: {px.sel(b, m) == Sb.read(W, k) : Maybe<&2, Nat>}) -> {m == Sb.read(List.append(&2, Sb.Doc, Sb.back.file(k, m), W), k) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      %ih : {None{} == _ : Maybe<&2, Nat>}
      px.sel_none(b)
    case Some{v}:
      %px.eq_refl(k) : {Some{v} == Sb.read.go(Sb.Doc{k, v} <> W, k, _) : Maybe<&2, Nat>}
      {==}

# a file added at another path is not read
def px.read_miss(+j: Nat, m: Maybe<&2, Nat>, +W: List<&2, Sb.Doc>, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.read(W, k) == Sb.read(List.append(&2, Sb.Doc, Sb.back.file(j, m), W), k) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      %Equal.sym(Bool, Nat.is_eq(j, k), False{}, ne) : {Sb.read(W, k) == Sb.read.go(Sb.Doc{j, v} <> W, k, _) : Maybe<&2, Nat>}
      {==}

def px.read_hit2(+k: Nat, +o: Sb.One, x: Sb.Back, +b: Bool, ih: {px.sel(b, Sb.One.body(o)) == Sb.read(Sb.Back.ws(x), k) : Maybe<&2, Nat>}) -> {Sb.One.body(o) == Sb.read(Sb.Back.ws(Sb.back.add(k, o, x)), k) : Maybe<&2, Nat>}:
  match x:
    case Sb.Back{w, c}:
      px.read_hit(k, Sb.One.body(o), w, b, ih)

def px.read_miss2(+j: Nat, +o: Sb.One, x: Sb.Back, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.read(Sb.Back.ws(x), k) == Sb.read(Sb.Back.ws(Sb.back.add(j, o, x)), k) : Maybe<&2, Nat>}:
  match x:
    case Sb.Back{w, c}:
      px.read_miss(j, Sb.One.body(o), w, k, ne)

def px.rb_go(+j: Nat, +rest: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, c: Bool, ec: {Nat.is_eq(j, k) == c : Bool}, ih: {px.sel(Sb.elem(rest, k), Sb.One.body(px.mk(par, base, child, k))) == Sb.read(Sb.Back.ws(Sb.back(rest, par, base, child)), k) : Maybe<&2, Nat>}) -> {px.sel(Bool.or(c, Sb.elem(rest, k)), Sb.One.body(px.mk(par, base, child, k))) == Sb.read(Sb.Back.ws(Sb.back(j <> rest, par, base, child)), k) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      %Equal.sym(Nat, j, k, px.eq_true(j, k, ec)) : {Sb.One.body(px.mk(par, base, child, k)) == Sb.read(Sb.Back.ws(Sb.back(_ <> rest, par, base, child)), k) : Maybe<&2, Nat>}
      px.read_hit2(k, px.mk(par, base, child, k), Sb.back(rest, par, base, child), Sb.elem(rest, k), ih)
    case False{}:
      %px.read_miss2(j, px.mk(par, base, child, j), Sb.back(rest, par, base, child), k, ec) : {px.sel(Sb.elem(rest, k), Sb.One.body(px.mk(par, base, child, k))) == _ : Maybe<&2, Nat>}
      ih

# the new workspace holds at k the merge of k, if k is listed
def px.read_back(ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat) -> {px.sel(Sb.elem(ks, k), Sb.One.body(px.mk(par, base, child, k))) == Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) : Maybe<&2, Nat>}:
  match ks:
    case Nil{}:
      {==}
    case +j <> +rest:
      px.rb_go(j, rest, par, base, child, k, Nat.is_eq(j, k), {==}, px.read_back(rest, par, base, child, k))

def px.cl_hit_go(+k: Nat, d: Bool, +cs: List<&2, Nat>, +b: Bool, ih: {Bool.and(b, d) == Sb.elem(cs, k) : Bool}) -> {d == Sb.elem(List.append(&2, Nat, Sb.back.clash(k, d), cs), k) : Bool}:
  match d:
    case True{}:
      %px.eq_refl(k) : {True{} == Bool.or(_, Sb.elem(cs, k)) : Bool}
      {==}
    case False{}:
      %ih : {False{} == _ : Bool}
      px.and_false(b)

def px.cl_miss_go(+j: Nat, d: Bool, +cs: List<&2, Nat>, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.elem(cs, k) == Sb.elem(List.append(&2, Nat, Sb.back.clash(j, d), cs), k) : Bool}:
  match d:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, k), False{}, ne) : {Sb.elem(cs, k) == Bool.or(_, Sb.elem(cs, k)) : Bool}
      {==}
    case False{}:
      {==}

def px.cl_hit(+k: Nat, +o: Sb.One, x: Sb.Back, +b: Bool, ih: {Bool.and(b, Sb.One.clash(o)) == Sb.elem(Sb.Back.clashes(x), k) : Bool}) -> {Sb.One.clash(o) == Sb.elem(Sb.Back.clashes(Sb.back.add(k, o, x)), k) : Bool}:
  match x:
    case Sb.Back{w, cs}:
      px.cl_hit_go(k, Sb.One.clash(o), cs, b, ih)

def px.cl_miss(+j: Nat, +o: Sb.One, x: Sb.Back, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.elem(Sb.Back.clashes(x), k) == Sb.elem(Sb.Back.clashes(Sb.back.add(j, o, x)), k) : Bool}:
  match x:
    case Sb.Back{w, cs}:
      px.cl_miss_go(j, Sb.One.clash(o), cs, k, ne)

def px.cb_go(+j: Nat, +rest: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, c: Bool, ec: {Nat.is_eq(j, k) == c : Bool}, ih: {Bool.and(Sb.elem(rest, k), Sb.One.clash(px.mk(par, base, child, k))) == Sb.elem(Sb.Back.clashes(Sb.back(rest, par, base, child)), k) : Bool}) -> {Bool.and(Bool.or(c, Sb.elem(rest, k)), Sb.One.clash(px.mk(par, base, child, k))) == Sb.elem(Sb.Back.clashes(Sb.back(j <> rest, par, base, child)), k) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, j, k, px.eq_true(j, k, ec)) : {Sb.One.clash(px.mk(par, base, child, k)) == Sb.elem(Sb.Back.clashes(Sb.back(_ <> rest, par, base, child)), k) : Bool}
      px.cl_hit(k, px.mk(par, base, child, k), Sb.back(rest, par, base, child), Sb.elem(rest, k), ih)
    case False{}:
      %px.cl_miss(j, px.mk(par, base, child, j), Sb.back(rest, par, base, child), k, ec) : {Bool.and(Sb.elem(rest, k), Sb.One.clash(px.mk(par, base, child, k))) == _ : Bool}
      ih

# k is a conflict iff it is listed and its merge clashes
def px.cl_back(ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat) -> {Bool.and(Sb.elem(ks, k), Sb.One.clash(px.mk(par, base, child, k))) == Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +j <> +rest:
      px.cb_go(j, rest, par, base, child, k, Nat.is_eq(j, k), {==}, px.cl_back(rest, par, base, child, k))
