# eukhe: the proof of LAW command_words_exact
#
# PROOF of LAW command_words_exact: induction on the line. A space starts a
# new (empty) word in front of the words of the rest, which render after
# it with a space; any other char joins the first word of the rest (never
# none: sp_words_ne), and is no space.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/whole.bend as CommandWhole
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ./base/space.bend as LACommandSpace

def pwe.render.at(b: Bool, +c: Nat, eb: {Nat.is_eq(c, 32n) == b : Bool}, W: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, ih: {Command.cmd_render(W) == r : List<&2, Nat>}, ne: {LACommandSpace.sp_ne(W) == True{} : Bool}) -> {Command.cmd_render(Cmd.words.at(b, c, W)) == c <> r : List<&2, Nat>}:
  match b:
    case True{}:
      match W:
        case Nil{}:
          LLogicLogic.cb_absurd({Command.cmd_render(Cmd.words.at(True{}, c, Nil{})) == c <> r : List<&2, Nat>}, ne)
        case Con{+w1, +rest}:
          %Equal.sym(Nat, c, 32n, LLogicNat.cb_nat_eq(c, 32n, eb)) : {32n <> List.append(&2, Nat, w1, Command.cmd_sep(rest)) == _ <> r : List<&2, Nat>}
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => 32n <> z, Command.cmd_render(w1 <> rest), r, ih)
    case False{}:
      match W:
        case Nil{}:
          LLogicLogic.cb_absurd({Command.cmd_render(Cmd.words.at(False{}, c, Nil{})) == c <> r : List<&2, Nat>}, ne)
        case Con{+w1, +rest}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => c <> z, Command.cmd_render(w1 <> rest), r, ih)

# the words of a line render to it
def pwe.render(line: List<&2, Nat>) -> {Command.cmd_render(Cmd.words(line)) == line : List<&2, Nat>}:
  match line:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      pwe.render.at(Nat.is_eq(c, 32n), c, {==}, Cmd.words(r), r, pwe.render(r), LACommandSpace.sp_words_ne(r))

def pwe.spaceless.at(b: Bool, +c: Nat, eb: {Nat.is_eq(c, 32n) == b : Bool}, W: List<&2, List<&2, Nat>>, ih: {Command.cmd_all_spaceless(W) == True{} : Bool}, ne: {LACommandSpace.sp_ne(W) == True{} : Bool}) -> {Command.cmd_all_spaceless(Cmd.words.at(b, c, W)) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      match W:
        case Nil{}:
          LLogicLogic.cb_absurd({Command.cmd_all_spaceless(Cmd.words.at(False{}, c, Nil{})) == True{} : Bool}, ne)
        case Con{+w1, +rest}:
          %Equal.sym(Bool, Nat.is_eq(c, 32n), False{}, eb) : {Bool.and(Bool.and(Bool.not(_), Command.cmd_spaceless(w1)), Command.cmd_all_spaceless(rest)) == True{} : Bool}
          ih

# the words of a line have no space
def pwe.spaceless(line: List<&2, Nat>) -> {Command.cmd_all_spaceless(Cmd.words(line)) == True{} : Bool}:
  match line:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      pwe.spaceless.at(Nat.is_eq(c, 32n), c, {==}, Cmd.words(r), pwe.spaceless(r), LACommandSpace.sp_words_ne(r))

def pwe.ne(ws: List<&2, List<&2, Nat>>, h: {LACommandSpace.sp_ne(ws) == True{} : Bool}) -> {List.is_empty(&2, List<&2, Nat>, ws) == False{} : Bool}:
  match ws:
    case Nil{}:
      LLogicLogic.cb_absurd({List.is_empty(&2, List<&2, Nat>, Nil{}) == False{} : Bool}, h)
    case Con{w, rest}:
      {==}

def CommandWhole.command_words_exact(line):
  +W = Cmd.words(line)
  %Equal.sym(List<&2, Nat>, Command.cmd_render(W), line, pwe.render(line)) : {(_, (Command.cmd_all_spaceless(W), List.is_empty(&2, List<&2, Nat>, W))) == (line, (True{}, False{})) : List<&2, Nat> & (Bool & Bool)}
  %Equal.sym(Bool, Command.cmd_all_spaceless(W), True{}, pwe.spaceless(line)) : {(line, (_, List.is_empty(&2, List<&2, Nat>, W))) == (line, (True{}, False{})) : List<&2, Nat> & (Bool & Bool)}
  %Equal.sym(Bool, List.is_empty(&2, List<&2, Nat>, W), False{}, pwe.ne(W, LACommandSpace.sp_words_ne(line))) : {(line, (True{}, _)) == (line, (True{}, False{})) : List<&2, Nat> & (Bool & Bool)}
  {==}
