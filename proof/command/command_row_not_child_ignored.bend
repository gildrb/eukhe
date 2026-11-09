# eukhe: the proof of LAW command_row_not_child_ignored
#
# PROOF of LAW command_row_not_child_ignored: the line keyed below q
# answers Tab and Enter through the row of the selection at q, with a row
# and with none (KB.kb_key); a place that holds no child of q gives no row
# (kr_miss_of), the same as no selection.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ./base.bend as LA
import ./base/keys.bend as KB
import ./command_stale_row_ignored.bend as PCommandStaleRowIgnored

def CommandNamed.command_row_not_child_ignored(t, pre, p, q, i, k, word, below, stale):
  +L = List.append(&2, Nat, pre, p)
  +w = word
  +b = below
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.Row{i}, k), Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), k, t, L, p), KB.kb_key(t, pre, p, q, Cmd.Row{i}, k, w, b)) : {_ == Cmd.key(t, L, Cmd.NoRow{}, k) : Cmd.Out}
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.NoRow{}, k), Cmd.key.row(Cmd.row(Cmd.NoRow{}, t, q), k, t, L, p), KB.kb_key(t, pre, p, q, Cmd.NoRow{}, k, w, b)) : {Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), k, t, L, p) == _ : Cmd.Out}
  %PCommandStaleRowIgnored.kr_miss_of(List.get(&2, Cmd.Ent, t, i), q, stale) : {Cmd.key.row(_, k, t, L, p) == Cmd.key.row(None{}, k, t, L, p) : Cmd.Out}
  {==}
