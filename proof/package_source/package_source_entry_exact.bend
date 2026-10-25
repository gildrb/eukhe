# eukhe: the proof of LAW package_source_entry_exact
#
# PROOF: each decoder stage's answer is the spelling of what it read (rix.*, from the wire exactness laws); an answer that is no error read a whole request with nothing left (rix.top).

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/ffi_package_source.bend as FPs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/package_source/model.bend as PackageSource
import ../../laws/package_source/entry.bend as PackageSourceEntry
import ./base/entry.bend as LE
import ../base/wire_dec.bend as LD

def PackageSourceEntry.package_source_entry_exact(s, ok):
  LE.rix.top(s, FPs.get_req(s), LE.rix.req_at(s, Wr.get_nat(s), LD.dcw.nat(s)), ok)
