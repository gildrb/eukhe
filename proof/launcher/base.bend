# eukhe: lemmas the proofs of area launcher share: logic, the entry reads
# back the answers the laws spell, its commit is the laws' "every answer
# is quiesced", and `at` changes worker i alone.

import Base
import ../../bend/ffi_launcher.bend as FLa
import ../../bend/launcher.bend as La
import ../../bend/wire.bend as Wr
import ../../laws/launcher.bend as Launcher

# Logic
# -----

def la.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# False is not True: anything follows
def la.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : la.BD(_, A, Unit)
  Unit{}

def la.MD(-A: Data, m: Maybe<&2, A>, t: Type, f: Type) -> Type:
  match m:
    case None{}:
      t
    case Some{x}:
      f

# None is not Some: anything follows
def la.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : la.MD(A, _, Unit, G)
  Unit{}

# the value of a Some, d for None
def la.val(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def la.some_inj(-A: Data, -x: A, -y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => la.val(A, x, m), Some{x}, Some{y}, e)

# The entry
# ---------

# the answers after the first read back, the first one being a
def la.bools_rt(t: List<&2, Bool>, +a: Bool, +rest: String) -> {Wr.Got{a <> t, rest} == FLa.get_answers.go(List.length(&2, Bool, t), Wr.get_bool(Wr.put_bool(a, Launcher.spell_bools(t, rest)))) : Wr.Dec<List<&2, Bool>>}:
  match t:
    case Nil{}:
      match a:
        case True{}:
          {==}
        case False{}:
          {==}
    case +x <> +u:
      match a:
        case True{}:
          %la.bools_rt(u, x, rest) : {Wr.Got{True{} <> x <> u, rest} == FLa.get_answers.cons(True{}, _) : Wr.Dec<List<&2, Bool>>}
          {==}
        case False{}:
          %la.bools_rt(u, x, rest) : {Wr.Got{False{} <> x <> u, rest} == FLa.get_answers.cons(False{}, _) : Wr.Dec<List<&2, Bool>>}
          {==}

# the commit is "every answer is quiesced"
def la.commits(xs: List<&2, Bool>) -> {Launcher.all_quiesced(xs) == La.commits(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case a <> t:
      %la.commits(t) : {Bool.and(a, Launcher.all_quiesced(t)) == Bool.and(a, _) : Bool}
      {==}

# the adoption of a worker that reports build n
def la.adopt_n(n: Nat) -> {FLa.put_adoption(La.adoption(0n, Some{n}), "") == Wr.put_nat(Launcher.adopt_spec(Some{n}), "") : String}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The workers
# -----------

# `at` puts f(w) at i, where ws has w
def la.at_here(~f: La.Wk -> La.Wk, i: Nat, ws: List<&2, La.Wk>, -w: La.Wk, at: {List.get(&2, La.Wk, ws, i) == Some{w} : Maybe<&2, La.Wk>}) -> {List.get(&2, La.Wk, La.at(~f, i, ws), i) == Some{f(w)} : Maybe<&2, La.Wk>}:
  match i ws:
    case 0n Nil{}:
      la.none_some(La.Wk, w, {List.get(&2, La.Wk, La.at(~f, 0n, Nil{}), 0n) == Some{f(w)} : Maybe<&2, La.Wk>}, at)
    case 0n x <> t:
      %Equal.sym(La.Wk, x, w, la.some_inj(La.Wk, x, w, at)) : {Some{f(_)} == Some{f(w)} : Maybe<&2, La.Wk>}
      {==}
    case 1n+j Nil{}:
      la.none_some(La.Wk, w, {List.get(&2, La.Wk, La.at(~f, 1n+j, Nil{}), 1n+j) == Some{f(w)} : Maybe<&2, La.Wk>}, at)
    case 1n+j x <> t:
      la.at_here(~f, j, t, w, at)
