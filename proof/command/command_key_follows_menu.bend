# eukhe: the proof of LAW command_key_follows_menu
#
# PROOF of LAW command_key_follows_menu: the line's words are pre's words
# and p (nm_words_last), so the menu and the key both act at the walk of
# pre's words (nm_menu_pre, nm_key_pre); a children menu of q comes only
# from a walk at q (nm_key_kids), whose key is the row of the selection
# at q, which is cmd_key_at (nm_key_row).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/named.bend as CommandNamed
import ./base/named.bend as LACommandNamed

def CommandNamed.command_key_follows_menu(t, pre, p, q, xs, sel, k, word, kids):
  +w2 = word
  +L = List.append(&2, Nat, pre, 32n <> p)
  +S = Cmd.walk(Cmd.words(pre), t, Cmd.Top{})
  +hk = Equal.trans(Cmd.Menu, Cmd.menu.at(S, t, p), Cmd.menu(t, L), Cmd.Kids{q, xs}, Equal.sym(Cmd.Menu, Cmd.menu(t, L), Cmd.menu.at(S, t, p), LACommandNamed.nm_menu_pre(t, pre, p, w2)), kids)
  %Equal.sym(Cmd.Out, Cmd.key(t, L, sel, k), Cmd.key.at(S, t, L, p, sel, k), LACommandNamed.nm_key_pre(t, pre, p, sel, k, w2)) : {_ == CommandNamed.cmd_key_at(t, q, L, p, sel, k) : Cmd.Out}
  LACommandNamed.nm_key_kids(S, t, L, p, sel, k, q, xs, hk)
