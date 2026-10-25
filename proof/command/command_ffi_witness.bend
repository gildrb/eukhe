# eukhe: the proof of LAW command_ffi_witness
#
# PROOF of LAW command_ffi_witness: the empty table with a resolve of the
# empty line fits, the empty input is malformed, and "x" is not empty:
# a closed computation.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../laws/command/entry.bend as Command

def Command.command_ffi_witness():
  (FCmd.Req{[], FCmd.QResolve{""}}, ("", ("x", {==})))
