# eukhe: the proof of LAW command_ffi_decides
#
# PROOF of LAW command_ffi_decides: the entry's own encoding of a request is its
# spelling (ce_req), so the entry answers the model's answer
# (command_ffi_answers), which is the spelled reply (ce_run).

import Base
import ../../bend/command.bend as Cmd
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LACommandEntry
import ./command_ffi_answers.bend as PCommandFfiAnswers


def Command.command_ffi_decides(r, h):
  %LACommandEntry.ce_req(r, "") : {FCmd.ffi(_) == Command.cmd_spell_reply(r) : String}
  Equal.trans(String, FCmd.ffi(FCmd.put_req(r, "")), FCmd.ffi.run(r), Command.cmd_spell_reply(r), Command.command_ffi_answers(r, h), LACommandEntry.ce_run(r))
