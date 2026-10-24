# eukhe: the proof of LAW command_ffi_spelled_left_over
#
# PROOF of LAW command_ffi_spelled_left_over: the spelling of a request is the entry's own
# encoding (ce_req), and that encoding with input left over is refused
# (command_ffi_left_over).

import Base
import ../../bend/command.bend as Cmd
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LACommandEntry
import ./command_ffi_left_over.bend as PCommandFfiLeftOver


def Command.command_ffi_spelled_left_over(r, rest, h, more):
  %LACommandEntry.ce_req(r, rest) : {FCmd.ffi(_) == Wr.err("command: input left over") : String}
  Command.command_ffi_left_over(r, rest, h, more)
