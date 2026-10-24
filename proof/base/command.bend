# eukhe: lemmas the proofs of two or more areas share: command

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ./logic/nat.bend as LLogicNat

# the model's same is cmd_eq
def cb_same(a: List<&2, Nat>, b: List<&2, Nat>) -> {Cmd.same(a, b) == Command.cmd_eq(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_same(xs, ys) : {Bool.and(Nat.is_eq(x, y), Cmd.same(xs, ys)) == Bool.and(Nat.is_eq(x, y), _) : Bool}
      {==}

def cb_same_eq(+a: List<&2, Nat>, +b: List<&2, Nat>, e: {Cmd.same(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  LLogicNat.cb_eq(a, b, Equal.trans(Bool, Command.cmd_eq(a, b), Cmd.same(a, b), True{}, Equal.sym(Bool, Cmd.same(a, b), Command.cmd_eq(a, b), cb_same(a, b)), e))

# the model's same_path is cmd_path_eq
def cb_same_path(a: List<&2, List<&2, Nat>>, b: List<&2, List<&2, Nat>>) -> {Cmd.same_path(a, b) == Command.cmd_path_eq(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_same(x, y) : {Bool.and(Cmd.same(x, y), Cmd.same_path(xs, ys)) == Bool.and(_, Command.cmd_path_eq(xs, ys)) : Bool}
      %cb_same_path(xs, ys) : {Bool.and(Cmd.same(x, y), Cmd.same_path(xs, ys)) == Bool.and(Cmd.same(x, y), _) : Bool}
      {==}

def cb_same_path_eq(+a: List<&2, List<&2, Nat>>, +b: List<&2, List<&2, Nat>>, e: {Cmd.same_path(a, b) == True{} : Bool}) -> {a == b : List<&2, List<&2, Nat>>}:
  LLogicNat.cb_path_eq(a, b, Equal.trans(Bool, Command.cmd_path_eq(a, b), Cmd.same_path(a, b), True{}, Equal.sym(Bool, Cmd.same_path(a, b), Command.cmd_path_eq(a, b), cb_same_path(a, b)), e))
