# eukhe: the proof of LAW command_enter_without_row
#
# PROOF of LAW command_enter_without_row: with no row, every walk state
# answers Enter through key.bare (the root and a walk find no row to
# pick), which is key.enter on the line's resolution; key.enter and
# cmd_enter_bare agree on each answer, the menu of a bare path because
# the model's join of a path is the spec's cmd_render of it (B.cb_join).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command.bend as Command
import ./base.bend as LA

# key.enter is cmd_enter_bare on every resolution
def kewr_enter(r: Cmd.Res, line: List<&2, Nat>) -> {Cmd.key.enter(r, line) == Command.cmd_enter_bare(r, line) : Cmd.Out}:
  match r:
    case Cmd.Runs{q, a}:
      {==}
    case Cmd.Opens{+q}:
      %LA.cb_join(q) : {Cmd.Out{List.append(&2, Nat, Cmd.join(q), [32n]), True{}, False{}} == Cmd.Out{List.append(&2, Nat, _, [32n]), True{}, False{}} : Cmd.Out}
      {==}
    case Cmd.Unknown{q, w}:
      {==}
    case Cmd.NoCmd{}:
      {==}

# at any walk state, Enter with no row is key.enter on the resolution
def kewr_at(s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>) -> {Cmd.key.at(s, t, line, p, Cmd.NoRow{}, Cmd.Enter{}) == Cmd.key.enter(Cmd.resolve(t, line), line) : Cmd.Out}:
  match s:
    case Cmd.Top{}:
      {==}
    case Cmd.Walk{q, e}:
      {==}
    case Cmd.Rest{q, ws}:
      {==}
    case Cmd.Lost{q, w}:
      {==}
    case Cmd.Stray{}:
      {==}

# whatever the line cuts into
def kewr_cut(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>) -> {Cmd.key.cut(c, t, line, Cmd.NoRow{}, Cmd.Enter{}) == Cmd.key.enter(Cmd.resolve(t, line), line) : Cmd.Out}:
  match c:
    case (d, p):
      kewr_at(Cmd.walk(d, t, Cmd.Top{}), t, line, p)

def Command.command_enter_without_row(t, line):
  %Equal.sym(Cmd.Out, Cmd.key.cut(Cmd.cut(Cmd.words(line)), t, line, Cmd.NoRow{}, Cmd.Enter{}), Cmd.key.enter(Cmd.resolve(t, line), line), kewr_cut(Cmd.cut(Cmd.words(line)), t, line)) : {_ == Command.cmd_enter_bare(Cmd.resolve(t, line), line) : Cmd.Out}
  kewr_enter(Cmd.resolve(t, line), line)
