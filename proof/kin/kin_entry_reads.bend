# eukhe: the proof of LAW kin_entry_reads
#
# PROOF: each decoder stage answers Got only for the spelling of its value, within the wire (kx.*, from wire_nat_exact, the string and list lemmas of proof/base/wire_dec.bend and proof/base/wire_strs.bend); a value is answered only for a request read whole (kx.top).

import Base
import ../../bend/kin.bend as K
import ../../bend/ffi_kin.bend as FK
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/kin.bend as Kin
import ./base/entry.bend as LE
import ../base/wire_dec.bend as LD


def Kin.kin_entry_reads(s, ok):
  LE.kx.top(s, FK.get_req(s), LE.kx.go(s, Wr.get_nat(s), LD.dcw.nat(s)), ok)
