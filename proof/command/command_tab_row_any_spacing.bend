# eukhe: the proof of LAW command_tab_row_any_spacing
#
# PROOF of LAW command_tab_row_any_spacing: a run of spaces gives empty
# words, so the words of the loose line are the words of q with empty
# words among them, then the last word p; its cut is those words and p
# (LSp.sp_cut). The walk skips an empty word at the root and at a
# declared path, so it lands where the walk over q lands, and the line
# answers through the row of the selection at q (LSp.sp_key). The place
# i holds e, a child of q, so the row is e (LA.kr_hit), and Tab on e is
# cmd_tab as on the single-spaced line (tcr_pick of
# command_tab_completes_row).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ./base.bend as LA
import ./base/space.bend as LSp
import ./command_tab_completes_row.bend as PCommandTabCompletesRow

def Command.command_tab_row_any_spacing(t, q, p, gs, i, e, ok, on, word, at, child):
  +l = Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs)
  %LSp.sp_key(t, q, p, gs, Cmd.Row{i}, Cmd.Tab{}, ok, on, word) : {_ == Command.cmd_tab(t, e) : Cmd.Out}
  %LA.kr_hit(t, q, i, e, at, child) : {Cmd.key.row(_, Cmd.Tab{}, t, l, p) == Command.cmd_tab(t, e) : Cmd.Out}
  PCommandTabCompletesRow.tcr_pick(e, t, l, p)
