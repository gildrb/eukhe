# PROOF of LAW command_menu_names_first_word: a spaceless line is one
# word (B.cb_words_one), so the cut has no words before the last and the
# menu is the command names.

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B

def Laws.command_menu_names_first_word(t, p, word):
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(p), [p], B.cb_words_one(p, word)) : {Cmd.menu.cut(Cmd.cut(_), t) == Cmd.Names{} : Cmd.Menu}
  {==}
