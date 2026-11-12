# eukhe: the proof of LAW command_enter_without_row_opens
#
# PROOF of LAW command_enter_without_row_opens: with no row, every walk
# state answers Enter with key.enter on the line's resolution (KB.kb_enter);
# for a bare path q whose menu opens that is q's line (the model's join, the
# spec's cmd_render: LA.cb_join) and a space, with the menu open.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ./base.bend as LA
import ./base/keys.bend as KB

def Command.command_enter_without_row_opens(t, line, q, opens):
  +R = {Cmd.Out{List.append(&2, Nat, Command.cmd_render(q), [32n]), True{}, False{}} : Cmd.Out}
  %Equal.sym(Cmd.Out, Cmd.key(t, line, Cmd.NoRow{}, Cmd.Enter{}), Cmd.key.enter(Cmd.resolve(t, line), line), KB.kb_enter(t, line)) : {_ == R : Cmd.Out}
  %Equal.sym(Cmd.Res, Cmd.resolve(t, line), Cmd.Opens{q}, opens) : {Cmd.key.enter(_, line) == R : Cmd.Out}
  %LA.cb_join(q) : {Cmd.Out{List.append(&2, Nat, Cmd.join(q), [32n]), True{}, False{}} == Cmd.Out{List.append(&2, Nat, _, [32n]), True{}, False{}} : Cmd.Out}
  {==}
