# eukhe: lemmas the proofs of area kernel_local share: the entry reads
# back the files the laws spell, and its reply writers write what the
# laws' spellers write.

import Base
import ../../bend/ffi_kernel_local.bend as FKL
import ../../bend/kernel_local.bend as KL
import ../../bend/wire.bend as Wr
import ../../laws/kernel_local.bend as KernelLocal

# Logic
# -----

def kl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# False is not True: anything follows
def kl.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : kl.BD(_, A, Unit)
  Unit{}

def kl.MD(-A: Data, m: Maybe<&2, A>, t: Type, f: Type) -> Type:
  match m:
    case None{}:
      t
    case Some{x}:
      f

# None is not Some: anything follows
def kl.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : kl.MD(A, _, Unit, G)
  Unit{}

# the value of a Some, d for None
def kl.val(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def kl.some_inj(-A: Data, -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => kl.val(A, x, m), Some{x}, Some{y}, e)

# a and b is True: a is True, b is True
def kl.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      kl.absurd({False{} == True{} : Bool}, e)

def kl.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      kl.absurd({b == True{} : Bool}, e)

# a file the laws spell reads back, whatever follows it
def kl.left_rt(l: KL.Left, rest: String) -> {Wr.Got{l, rest} == FKL.get_left(KernelLocal.spell_left(l, rest)) : Wr.Dec<KL.Left>}:
  match l:
    case KL.Left{k, o}:
      match k o:
        case KL.Cand{} KL.Alive{}:
          {==}
        case KL.Cand{} KL.Dead{}:
          {==}
        case KL.Aside{} KL.Alive{}:
          {==}
        case KL.Aside{} KL.Dead{}:
          {==}
        case KL.Foreign{} KL.Alive{}:
          {==}
        case KL.Foreign{} KL.Dead{}:
          {==}

# the files after the first read back, the first one being l
def kl.lefts_rt(t: List<&2, KL.Left>, +l: KL.Left, +rest: String) -> {Wr.Got{l <> t, rest} == FKL.get_lefts.go(List.length(&2, KL.Left, t), FKL.get_left(KernelLocal.spell_left(l, KernelLocal.spell_lefts(t, rest)))) : Wr.Dec<List<&2, KL.Left>>}:
  match t:
    case Nil{}:
      %kl.left_rt(l, rest) : {Wr.Got{[l], rest} == FKL.get_lefts.go(0n, _) : Wr.Dec<List<&2, KL.Left>>}
      {==}
    case +x <> +u:
      %kl.left_rt(l, KernelLocal.spell_left(x, KernelLocal.spell_lefts(u, rest))) : {Wr.Got{l <> x <> u, rest} == FKL.get_lefts.go(1n+List.length(&2, KL.Left, u), _) : Wr.Dec<List<&2, KL.Left>>}
      %kl.lefts_rt(u, x, rest) : {Wr.Got{l <> x <> u, rest} == FKL.get_lefts.cons(l, _) : Wr.Dec<List<&2, KL.Left>>}
      {==}

# the entry writes each verdict as the laws spell it
def kl.bools_items(bs: List<&2, Bool>, -rest: String) -> {FKL.put_bools.items(bs, rest) == KernelLocal.spell_bools(bs, rest) : String}:
  match bs:
    case Nil{}:
      {==}
    case b <> t:
      %kl.bools_items(t, rest) : {Wr.put_bool(b, FKL.put_bools.items(t, rest)) == Wr.put_bool(b, _) : String}
      {==}

# the entry writes an end as the laws spell it
def kl.end(e: KL.End, -rest: String) -> {FKL.put_end(e, rest) == KernelLocal.spell_end(e, rest) : String}:
  match e:
    case KL.Got{}:
      {==}
    case KL.Busy{}:
      {==}
    case KL.Freed{}:
      {==}
    case KL.Crash{}:
      {==}
