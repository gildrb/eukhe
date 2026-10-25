# eukhe: the proof of LAW command_row_ignored_shut_menu
#
# PROOF of LAW command_row_ignored_shut_menu: the menu and the key act at
# the walk of pre's words (nm_menu_pre, nm_key_pre); a line that is not
# blank walks off the root (nm_off_pre), and off the root a shut menu
# means argument text, an unknown word or a stray word, where every
# selection answers as no row (nm_key_shut).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/named.bend as CommandNamed
import ./base/named.bend as LACommandNamed

def CommandNamed.command_row_ignored_shut_menu(t, pre, p, i, k, word, typed, shut):
  +w2 = word
  +L = List.append(&2, Nat, pre, 32n <> p)
  +S = Cmd.walk(Cmd.words(pre), t, Cmd.Top{})
  +hs = Equal.trans(Cmd.Menu, Cmd.menu.at(S, t, p), Cmd.menu(t, L), Cmd.Shut{}, Equal.sym(Cmd.Menu, Cmd.menu(t, L), Cmd.menu.at(S, t, p), LACommandNamed.nm_menu_pre(t, pre, p, w2)), shut)
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.Row{i}, k), Cmd.key.at(S, t, L, p, Cmd.Row{i}, k), LACommandNamed.nm_key_pre(t, pre, p, Cmd.Row{i}, k, w2)) : {_ == Cmd.key(t, L, Cmd.NoRow{}, k) : Cmd.Out}
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.NoRow{}, k), Cmd.key.at(S, t, L, p, Cmd.NoRow{}, k), LACommandNamed.nm_key_pre(t, pre, p, Cmd.NoRow{}, k, w2)) : {Cmd.key.at(S, t, L, p, Cmd.Row{i}, k) == _ : Cmd.Out}
  LACommandNamed.nm_key_shut(S, t, L, p, i, k, hs, LACommandNamed.nm_off_pre(t, pre, typed))
