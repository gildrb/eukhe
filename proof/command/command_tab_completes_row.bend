# eukhe: the proof of LAW command_tab_completes_row
#
# PROOF of LAW command_tab_completes_row: the line q p answers through
# the row of the selection at q (KR.kr_key); the place i holds e, a
# child of q, so the row is e and Tab picks it (KR.kr_hit). key.tab on e
# and cmd_tab agree: kids.any is cmd_has_kid, join is cmd_render, and
# spaced is cmd_space_if.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command.bend as Command
import ./base.bend as LA

def tcr_spaced(b: Bool, l: List<&2, Nat>) -> {Cmd.spaced(b, l) == Command.cmd_space_if(b, l) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Tab on the row e is cmd_tab
def tcr_pick(e: Cmd.Ent, +t: List<&2, Cmd.Ent>, line: List<&2, Nat>, p: List<&2, Nat>) -> {Cmd.key.pick(Cmd.Tab{}, e, t, line, p) == Command.cmd_tab(t, e) : Cmd.Out}:
  match e:
    case Cmd.Ent{+pp, a, r, f, +g}:
      %LA.cb_kids_any(t, pp) : {Cmd.Out{Cmd.spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)), Cmd.kids.any(t, pp), False{}} == Cmd.Out{Command.cmd_space_if(Bool.or(_, g), Command.cmd_render(pp)), _, False{}} : Cmd.Out}
      %LA.cb_join(pp) : {Cmd.Out{Cmd.spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)), Cmd.kids.any(t, pp), False{}} == Cmd.Out{Command.cmd_space_if(Bool.or(Cmd.kids.any(t, pp), g), _), Cmd.kids.any(t, pp), False{}} : Cmd.Out}
      %tcr_spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)) : {Cmd.Out{Cmd.spaced(Bool.or(Cmd.kids.any(t, pp), g), Cmd.join(pp)), Cmd.kids.any(t, pp), False{}} == Cmd.Out{_, Cmd.kids.any(t, pp), False{}} : Cmd.Out}
      {==}

def Command.command_tab_completes_row(t, q, p, i, e, ok, on, word, at, child):
  %LA.kr_key(t, q, p, Cmd.Row{i}, Cmd.Tab{}, ok, on, word) : {_ == Command.cmd_tab(t, e) : Cmd.Out}
  %LA.kr_hit(t, q, i, e, at, child) : {Cmd.key.row(_, Cmd.Tab{}, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Command.cmd_tab(t, e) : Cmd.Out}
  tcr_pick(e, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p)
