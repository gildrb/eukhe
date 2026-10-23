# eukhe: the proof of LAW command_menu_names_first_word
#
# PROOF of LAW command_menu_names_first_word: a spaceless line is one
# word (B.cb_words_one), so the cut has no words before the last and the
# menu is the command names.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command.bend as Command
import ../base/bool.bend as LBool
import ./base.bend as LA

# the words of a spaceless word: itself
def cb_words_one(+p: List<&2, Nat>, h: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(p) == [p] : List<&2, List<&2, Nat>>}:
  %LA.cb_app_nil(Nat, p) : {Cmd.words(_) == [p] : List<&2, List<&2, Nat>>}
  LA.cb_words_render(p, Nil{}, LBool.cb_and_intro(Command.cmd_spaceless(p), True{}, h, {==}))

def Command.command_menu_names_first_word(t, p, word):
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(p), [p], cb_words_one(p, word)) : {Cmd.menu.cut(Cmd.cut(_), t) == Cmd.Names{} : Cmd.Menu}
  {==}
