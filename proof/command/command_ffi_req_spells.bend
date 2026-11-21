# eukhe: the proof of LAW command_ffi_req_spells
#
# PROOF of LAW command_ffi_req_spells: piece by piece, the request encoder
# writes what the spec speller spells (LACommandEntry.ce_req: the table,
# each entry, the question, the row and the key), for every request.

import Base
import ../../laws/command/entry.bend as Command
import ./base/entry.bend as LACommandEntry

def Command.command_ffi_req_spells(r, rest):
  LACommandEntry.ce_req(r, rest)
