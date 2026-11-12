# eukhe: lemmas of area call_lift about the arguments: the code's `has`
# is "the names do not lack k" (CallLift.lacks over CallLift.keys_of), an
# argument named k found after arguments named otherwise makes `has`
# true, and the code's rename renames exactly that argument in place

import Base
import ../../../bend/call_lift.bend as Cl
import ../../../laws/call_lift.bend as CallLift
import ../../base/staging.bend as LStg
import ./string.bend as LCallLiftString

def cll.key(a: Cl.Arg) -> {Cl.arg_key(a) == CallLift.key_of(a) : String}:
  match a:
    case Cl.Kept{i, k}:
      {==}
    case Cl.Added{k, j}:
      {==}

def cll.or_not(b: Bool, -q: Bool, -r: Bool, ih: {q == Bool.not(r) : Bool}) -> {Bool.or(b, q) == Bool.not(Bool.and(Bool.not(b), r)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def cll.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# some argument is named k exactly when the names do not lack k
def cll.has(+args: List<&2, Cl.Arg>, +k: String) -> {Cl.has(args, k) == Bool.not(CallLift.lacks(CallLift.keys_of(args), k)) : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{+a, +rest}:
      %Equal.sym(String, Cl.arg_key(a), CallLift.key_of(a), cll.key(a)) : {Bool.or(String.eq(_, k), Cl.has(rest, k)) == Bool.not(Bool.and(Bool.not(String.eq(CallLift.key_of(a), k)), CallLift.lacks(CallLift.keys_of(rest), k))) : Bool}
      cll.or_not(String.eq(CallLift.key_of(a), k), Cl.has(rest, k), CallLift.lacks(CallLift.keys_of(rest), k), cll.has(rest, k))

# has, read off what the names say about k
def cll.has_is(+args: List<&2, Cl.Arg>, +k: String, -b: Bool, e: {CallLift.lacks(CallLift.keys_of(args), k) == b : Bool}) -> {Cl.has(args, k) == Bool.not(b) : Bool}:
  Equal.trans(Bool, Cl.has(args, k), Bool.not(CallLift.lacks(CallLift.keys_of(args), k)), Bool.not(b), cll.has(args, k), Equal.cong(Bool, Bool, z => Bool.not(z), CallLift.lacks(CallLift.keys_of(args), k), b, e))

# an argument named k, after any others, makes has true
def cll.has_at(+pre: List<&2, Cl.Arg>, +x: Cl.Arg, post: List<&2, Cl.Arg>, +k: String, named: {CallLift.key_of(x) == k : String}) -> {Cl.has(List.append(&2, Cl.Arg, pre, x <> post), k) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(String, Cl.arg_key(x), CallLift.key_of(x), cll.key(x)) : {Bool.or(String.eq(_, k), Cl.has(post, k)) == True{} : Bool}
      %Equal.sym(String, CallLift.key_of(x), k, named) : {Bool.or(String.eq(_, k), Cl.has(post, k)) == True{} : Bool}
      %LCallLiftString.clm.str_refl_sym(k) : {Bool.or(_, Cl.has(post, k)) == True{} : Bool}
      {==}
    case Con{+a, +rest}:
      %Equal.sym(Bool, Cl.has(List.append(&2, Cl.Arg, rest, x <> post), k), True{}, cll.has_at(rest, x, post, k, named)) : {Bool.or(String.eq(Cl.arg_key(a), k), _) == True{} : Bool}
      cll.or_true(String.eq(Cl.arg_key(a), k))

def cll.named(x: Cl.Arg, -to: String, -post: List<&2, Cl.Arg>) -> {Cl.arg_named(x, to) <> post == CallLift.renamed(x, to) <> post : List<&2, Cl.Arg>}:
  match x:
    case Cl.Kept{i, k}:
      {==}
    case Cl.Added{k, j}:
      {==}

# an argument the premise says is not named from stays in place
def cll.rename_skip(b: Bool, +a: Cl.Arg, -tail: List<&2, Cl.Arg>, -mv: List<&2, Cl.Arg>, -want: List<&2, Cl.Arg>, -q: Bool, -to: String, h: {Bool.and(Bool.not(b), q) == True{} : Bool}, ih: {q == True{} : Bool} -> {mv == want : List<&2, Cl.Arg>}) -> {Cl.rename.at(b, a, tail, mv, to) == a <> want : List<&2, Cl.Arg>}:
  match b:
    case True{}:
      LStg.stg.absurd({Cl.rename.at(True{}, a, tail, mv, to) == a <> want : List<&2, Cl.Arg>}, Equal.sym(Bool, False{}, True{}, h))
    case False{}:
      Equal.cong(List<&2, Cl.Arg>, List<&2, Cl.Arg>, z => a <> z, mv, want, ih(h))

# the first argument named from (x, after arguments pre named otherwise)
# is renamed in place, every other argument kept
def cll.rename_at(+pre: List<&2, Cl.Arg>, +x: Cl.Arg, +post: List<&2, Cl.Arg>, +from: String, +to: String, named: {CallLift.key_of(x) == from : String}, before: {CallLift.lacks(CallLift.keys_of(pre), from) == True{} : Bool}) -> {Cl.rename(List.append(&2, Cl.Arg, pre, x <> post), from, to) == List.append(&2, Cl.Arg, pre, CallLift.renamed(x, to) <> post) : List<&2, Cl.Arg>}:
  match pre:
    case Nil{}:
      %Equal.sym(String, Cl.arg_key(x), CallLift.key_of(x), cll.key(x)) : {Cl.rename.at(String.eq(_, from), x, post, Cl.rename(post, from, to), to) == CallLift.renamed(x, to) <> post : List<&2, Cl.Arg>}
      %Equal.sym(String, CallLift.key_of(x), from, named) : {Cl.rename.at(String.eq(_, from), x, post, Cl.rename(post, from, to), to) == CallLift.renamed(x, to) <> post : List<&2, Cl.Arg>}
      %LCallLiftString.clm.str_refl_sym(from) : {Cl.rename.at(_, x, post, Cl.rename(post, from, to), to) == CallLift.renamed(x, to) <> post : List<&2, Cl.Arg>}
      cll.named(x, to, post)
    case Con{+a, +rest}:
      %Equal.sym(String, Cl.arg_key(a), CallLift.key_of(a), cll.key(a)) : {Cl.rename.at(String.eq(_, from), a, List.append(&2, Cl.Arg, rest, x <> post), Cl.rename(List.append(&2, Cl.Arg, rest, x <> post), from, to), to) == a <> List.append(&2, Cl.Arg, rest, CallLift.renamed(x, to) <> post) : List<&2, Cl.Arg>}
      cll.rename_skip(String.eq(CallLift.key_of(a), from), a, List.append(&2, Cl.Arg, rest, x <> post), Cl.rename(List.append(&2, Cl.Arg, rest, x <> post), from, to), List.append(&2, Cl.Arg, rest, CallLift.renamed(x, to) <> post), CallLift.lacks(CallLift.keys_of(rest), from), to, before, h => cll.rename_at(rest, x, post, from, to, named, h))
