# eukhe: lemmas the proofs of area staging share

import Base
import ../../bend/staging.bend as Sg

# ---- staging ----

# proof_staging: the staging, sweep and listing laws of LAWS.bend section storage
# (D2): a publish never takes a name that is taken; a sweep never removes
# a held, young or unreached entry, and removes every stale free leftover
# it reaches; a session is listed once, under the storage it opens as.

# Logic and numbers
# -----------------

def pg.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pg.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pg.BD(_, Unit, A)
  Unit{}

def pg.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pg.absurd({0n == 1n+q : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 0n:
      pg.absurd({1n+p == 0n : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      %pg.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def pg.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pg.eq_refl(p)

# Sweep
# -----

def pg.put_app(+n: Sg.Node, a: List<&2, Sg.Node>, +c: List<&2, Sg.Node>, b: Bool) -> {Sg.sweep.put(n, List.append(&2, Sg.Node, a, c), b) == List.append(&2, Sg.Node, Sg.sweep.put(n, a, b), c) : List<&2, Sg.Node>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.sweep_app(pre: List<&2, Sg.Node>, +x: List<&2, Sg.Node>) -> {List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(x)) == Sg.sweep(List.append(&2, Sg.Node, pre, x)) : List<&2, Sg.Node>}:
  match pre:
    case Nil{}:
      {==}
    case +n <> +rest:
      %pg.put_app(n, Sg.sweep(rest), Sg.sweep(x), Sg.removes(n)) : {_ == Sg.sweep.put(n, Sg.sweep(List.append(&2, Sg.Node, rest, x)), Sg.removes(n)) : List<&2, Sg.Node>}
      %pg.sweep_app(rest, x) : {Sg.sweep.put(n, List.append(&2, Sg.Node, Sg.sweep(rest), Sg.sweep(x)), Sg.removes(n)) == Sg.sweep.put(n, _, Sg.removes(n)) : List<&2, Sg.Node>}
      {==}

# a node the sweep keeps: the sweep of the whole is the sweep of the parts
def pg.kept(+pre: List<&2, Sg.Node>, +n: Sg.Node, +post: List<&2, Sg.Node>, no: {False{} == Sg.removes(n) : Bool}) -> {Sg.sweep(List.append(&2, Sg.Node, pre, n <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  %pg.sweep_app(pre, n <> post) : {_ == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}
  %no : {List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep.put(n, Sg.sweep(post), _)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}
  {==}

# An import
# ---------

def pg.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.mem_app(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {Bool.or(Sg.mem(n, a), Sg.mem(n, b)) == Sg.mem(n, List.append(&2, Nat, a, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +rest:
      %pg.mem_app(n, rest, b) : {Bool.or(Bool.or(Nat.is_eq(x, n), Sg.mem(n, rest)), Sg.mem(n, b)) == Bool.or(Nat.is_eq(x, n), _) : Bool}
      pg.or_assoc(Nat.is_eq(x, n), Sg.mem(n, rest), Sg.mem(n, b))

def pg.kput_app(+m: Nat, a: List<&2, Nat>, +c: List<&2, Nat>, q: Bool) -> {Sg.keep.put(m, List.append(&2, Nat, a, c), q) == List.append(&2, Nat, Sg.keep.put(m, a, q), c) : List<&2, Nat>}:
  match q:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.dur_app(es: List<&2, Sg.Ent>, +x: List<&2, Sg.Ent>) -> {List.append(&2, Nat, Sg.durables(es), Sg.durables(x)) == Sg.durables(List.append(&2, Sg.Ent, es, x)) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Sg.Dir{+m, +a, +hd, +c}:
          +q = Bool.and(a, Bool.and(Bool.not(hd), c))
          %pg.kput_app(m, Sg.durables(rest), Sg.durables(x), q) : {_ == Sg.keep.put(m, Sg.durables(List.append(&2, Sg.Ent, rest, x)), q) : List<&2, Nat>}
          %pg.dur_app(rest, x) : {Sg.keep.put(m, List.append(&2, Nat, Sg.durables(rest), Sg.durables(x)), q) == Sg.keep.put(m, _, q) : List<&2, Nat>}
          {==}
        case Sg.Legacy{s, r}:
          pg.dur_app(rest, x)
