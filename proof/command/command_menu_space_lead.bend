# eukhe: the proof of LAW command_menu_space_lead
#
# PROOF of LAW command_menu_space_lead: a line with a space has two or
# more words (msl_words_two: a space starts a word after the words
# before it, and the words of a line are never none), and a leading
# space adds one empty first word. With two or more words the cut keeps
# the first word, so the words before the last stay not none with or
# without the empty word before them; the menu walks them from the root,
# where the empty word changes nothing (step.empty of Top is Top), and
# both menus compute to the same term.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./base/space.bend as LSp

# two or more words
def msl_two(ws: List<&2, List<&2, Nat>>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w, rest}:
      LSp.sp_ne(rest)

def msl_two_put(-c: Nat, ws: List<&2, List<&2, Nat>>, h: {msl_two(ws) == True{} : Bool}) -> {msl_two(Cmd.put_word(c, ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      LLogicLogic.cb_absurd({msl_two(Cmd.put_word(c, Nil{})) == True{} : Bool}, h)
    case Con{w, rest}:
      h

def msl_two_at(b: Bool, -c: Nat, r: List<&2, Nat>, h: {Bool.and(Bool.not(b), Command.cmd_spaceless(r)) == False{} : Bool}, ih: {Command.cmd_spaceless(r) == False{} : Bool} -> {msl_two(Cmd.words(r)) == True{} : Bool}) -> {msl_two(Cmd.words.at(b, c, Cmd.words(r))) == True{} : Bool}:
  match b:
    case True{}:
      LSp.sp_words_ne(r)
    case False{}:
      msl_two_put(c, Cmd.words(r), ih(h))

# a line with a space has two or more words
def msl_words_two(line: List<&2, Nat>, h: {Command.cmd_spaceless(line) == False{} : Bool}) -> {msl_two(Cmd.words(line)) == True{} : Bool}:
  match line:
    case Nil{}:
      LA.cb_absurd2({msl_two(Cmd.words(Nil{})) == True{} : Bool}, h)
    case Con{+c, +r}:
      msl_two_at(Nat.is_eq(c, 32n), c, r, h, e => msl_words_two(r, e))

def msl_pair(c: List<&2, List<&2, Nat>> & List<&2, Nat>, -a: List<&2, Nat>, +t: List<&2, Cmd.Ent>) -> {Cmd.menu.cut(Cmd.cut.cons(Nil{}, Cmd.cut.cons(a, c)), t) == Cmd.menu.cut(Cmd.cut.cons(a, c), t) : Cmd.Menu}:
  match c:
    case (d, p):
      {==}

# an empty first word before two or more words changes nothing the menu
def msl_lead(ws: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, h: {msl_two(ws) == True{} : Bool}) -> {Cmd.menu.cut(Cmd.cut(Nil{} <> ws), t) == Cmd.menu.cut(Cmd.cut(ws), t) : Cmd.Menu}:
  match ws:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.menu.cut(Cmd.cut([Nil{}]), t) == Cmd.menu.cut(Cmd.cut(Nil{}), t) : Cmd.Menu}, h)
    case Con{a, rest}:
      match rest:
        case Nil{}:
          LLogicLogic.cb_absurd({Cmd.menu.cut(Cmd.cut([Nil{}, a]), t) == Cmd.menu.cut(Cmd.cut([a]), t) : Cmd.Menu}, h)
        case Con{b, more}:
          msl_pair(Cmd.cut.go(more, b), a, t)

def Command.command_menu_space_lead(t, line, two):
  msl_lead(Cmd.words(line), t, msl_words_two(line, two))
