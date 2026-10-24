# eukhe: the proof of LAW command_stale_row_any_spacing
#
# PROOF of LAW command_stale_row_any_spacing: the loose line cuts into
# the words of q with empty words among them and the last word p
# (LSp.sp_cut); the walk skips the empty words at the root and at a
# declared path, so with the place i and with no row alike the line
# answers through the row of the selection at q (LSp.sp_key). A place
# that holds no child of q gives no row (kr_miss_of of
# command_stale_row_ignored), the same as no selection.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ./base/space.bend as LSp
import ./command_stale_row_ignored.bend as PCommandStaleRowIgnored

def Command.command_stale_row_any_spacing(t, q, p, gs, i, k, ok, on, word, stale):
  +o = ok
  +n = on
  +w = word
  +l = Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs)
  %LSp.sp_key(t, q, p, gs, Cmd.Row{i}, k, o, n, w) : {_ == Cmd.key(t, l, Cmd.NoRow{}, k) : Cmd.Out}
  %LSp.sp_key(t, q, p, gs, Cmd.NoRow{}, k, o, n, w) : {Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), k, t, l, p) == _ : Cmd.Out}
  %PCommandStaleRowIgnored.kr_miss_of(List.get(&2, Cmd.Ent, t, i), q, stale) : {Cmd.key.row(_, k, t, l, p) == Cmd.key.row(None{}, k, t, l, p) : Cmd.Out}
  {==}
