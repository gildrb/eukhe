# eukhe: the proof of LAW command_menu_space_lead_word
#
# PROOF of LAW command_menu_space_lead_word: the words of a spaceless
# word p are [p] (LA.cb_words_app), so the words of a space and p are an
# empty word and p; the cut keeps the empty word before p, the walk over
# it stays at the root (step.empty of Top is Top), and the root shows no
# menu below a word (menu.at of Top is Shut).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ./base.bend as LA

# the words of a spaceless word are that word
def mlw_words(+p: List<&2, Nat>, h: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(p) == [p] : List<&2, List<&2, Nat>>}:
  %LA.cb_app_nil(Nat, p) : {Cmd.words(p) == [_] : List<&2, List<&2, Nat>>}
  %LA.cb_put_con(p, Nil{}, Nil{}) : {Cmd.words(p) == _ : List<&2, List<&2, Nat>>}
  %LA.cb_words_app(p, Nil{}, h) : {Cmd.words(p) == _ : List<&2, List<&2, Nat>>}
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, p, Nil{}), p, LA.cb_app_nil(Nat, p)) : {Cmd.words(p) == Cmd.words(_) : List<&2, List<&2, Nat>>}
  {==}

def Command.command_menu_space_lead_word(t, p, word):
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(p), [p], mlw_words(p, word)) : {Cmd.menu.cut(Cmd.cut(Nil{} <> _), t) == Cmd.Shut{} : Cmd.Menu}
  {==}
