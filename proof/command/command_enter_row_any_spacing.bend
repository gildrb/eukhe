# eukhe: the proof of LAW command_enter_row_any_spacing
#
# PROOF of LAW command_enter_row_any_spacing: the loose line cuts into
# the words of q with empty words among them and the last word p
# (LSp.sp_cut); the walk skips the empty words at the root and at a
# declared path, so it lands where the walk over q lands, and the line
# answers through the row of the selection at q (LSp.sp_key), with the
# line itself passed through. The place i holds e, a child of q, so the
# row is e (LA.kr_hit), and Enter on e with the typed word p and the
# loose line is cmd_enter of that line (eor_pick of
# command_enter_on_row, which holds for any line).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ./base.bend as LA
import ./base/space.bend as LSp
import ./command_enter_on_row.bend as PCommandEnterOnRow

def Command.command_enter_row_any_spacing(t, q, p, gs, i, e, ok, on, word, at, child):
  +l = Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs)
  %LSp.sp_key(t, q, p, gs, Cmd.Row{i}, Cmd.Enter{}, ok, on, word) : {_ == Command.cmd_enter(t, e, p, l) : Cmd.Out}
  %LA.kr_hit(t, q, i, e, at, child) : {Cmd.key.row(_, Cmd.Enter{}, t, l, p) == Command.cmd_enter(t, e, p, l) : Cmd.Out}
  PCommandEnterOnRow.eor_pick(e, t, l, p)
