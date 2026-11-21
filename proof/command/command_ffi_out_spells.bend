# eukhe: the proof of LAW command_ffi_out_spells
#
# PROOF of LAW command_ffi_out_spells: the key reply encoder is the
# speller, field by field.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../laws/command/entry.bend as Command

def Command.command_ffi_out_spells(x, rest):
  match x:
    case FCmd.OutW{l, a, b}:
      {==}
