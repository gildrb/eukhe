# eukhe: the proof of LAW redirect_input_entry_exact
#
# PROOF: each decoder stage's answer is the spelling of what it read (rix.*, from the wire exactness laws); an answer that is no error read a whole request with nothing left (rix.top).

import Base
import ../../bend/redirect_input.bend as Ri
import ../../bend/ffi_redirect_input.bend as FRi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/redirect_input.bend as RedirectInput
import ./base/entry.bend as LE
import ../base/wire_dec.bend as LD

def RedirectInput.redirect_input_entry_exact(s, ok):
  LE.rix.top(s, FRi.get_req(s), LE.rix.req_at(s, Wr.get_nat(s), LD.dcw.nat(s)), ok)
