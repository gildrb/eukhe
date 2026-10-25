# eukhe: the proof of LAW glob_entry_exact
#
# PROOF: each decoder stage answers Got only for the spelling of what it read so far, every count and length within the wire (ge.x.*, from wire_nat_exact, wire_bool_exact, wire_str_exact, wire_strs_exact and wire_list_exact with their fits; a list of Nats by ge.nats_fit); a value is answered only for a request read whole with nothing left.

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/entry.bend as GE

def Glob.glob_entry_exact(s, ok):
  GE.ge.x.top(s, FG.get_req(s), GE.ge.x.tag(s, Wr.get_nat(s), {==}), ok)
