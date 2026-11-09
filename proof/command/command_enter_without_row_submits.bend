# eukhe: the proof of LAW command_enter_without_row_submits
#
# PROOF of LAW command_enter_without_row_submits: with no row, every walk
# state answers Enter with key.enter on the line's resolution (KB.kb_enter);
# a resolution that opens no menu (a run, an unknown word, no command)
# submits the line as it is.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ./base.bend as LA
import ./base/keys.bend as KB

def ews_at(r: Cmd.Res, +line: List<&2, Nat>, h: {Command.cmd_opens(r) == False{} : Bool}) -> {Cmd.key.enter(r, line) == Cmd.Out{line, False{}, True{}} : Cmd.Out}:
  match r:
    case Cmd.Runs{q, a}:
      {==}
    case Cmd.Opens{q}:
      LA.cb_absurd2({Cmd.key.enter(Cmd.Opens{q}, line) == Cmd.Out{line, False{}, True{}} : Cmd.Out}, h)
    case Cmd.Unknown{q, w}:
      {==}
    case Cmd.NoCmd{}:
      {==}

def Command.command_enter_without_row_submits(t, line, runs):
  %Equal.sym(Cmd.Out, Cmd.key(t, line, Cmd.NoRow{}, Cmd.Enter{}), Cmd.key.enter(Cmd.resolve(t, line), line), KB.kb_enter(t, line)) : {_ == Cmd.Out{line, False{}, True{}} : Cmd.Out}
  ews_at(Cmd.resolve(t, line), line, runs)
